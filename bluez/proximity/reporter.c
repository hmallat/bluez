/*
 *
 *  BlueZ - Bluetooth protocol stack for Linux
 *
 *  Copyright (C) 2011  Nokia Corporation
 *  Copyright (C) 2011  Marcel Holtmann <marcel@holtmann.org>
 *
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <glib.h>
#include <bluetooth/uuid.h>
#include <adapter.h>
#include <errno.h>

#include <dbus/dbus.h>
#include <gdbus.h>

#include "log.h"

#include "dbus-common.h"
#include "error.h"
#include "device.h"
#include "hcid.h"
#include "gattrib.h"
#include "att.h"
#include "gatt.h"
#include "att-database.h"
#include "attrib-server.h"
#include "reporter.h"
#include "linkloss.h"
#include "immalert.h"

#define BLUEZ_SERVICE "org.bluez"

struct reporter_adapter {
	DBusConnection *conn;
	struct btd_adapter *adapter;
	GSList *devices;
};

static GSList *reporter_adapters;

static int radapter_cmp(gconstpointer a, gconstpointer b)
{
	const struct reporter_adapter *radapter = a;
	const struct btd_adapter *adapter = b;

	if (radapter->adapter == adapter)
		return 0;

	return -1;
}

static struct reporter_adapter *
find_reporter_adapter(struct btd_adapter *adapter)
{
	GSList *l = g_slist_find_custom(reporter_adapters, adapter,
								radapter_cmp);
	if (!l)
		return NULL;

	return l->data;
}

const char *get_alert_level_string(uint8_t level)
{
	switch (level) {
	case NO_ALERT:
		return "none";
	case MILD_ALERT:
		return "mild";
	case HIGH_ALERT:
		return "high";
	}

	return "unknown";
}

static void register_tx_power(struct btd_adapter *adapter)
{
	uint16_t start_handle, h;
	const int svc_size = 4;
	uint8_t atval[256];
	bt_uuid_t uuid;

	bt_uuid16_create(&uuid, TX_POWER_SVC_UUID);
	start_handle = attrib_db_find_avail(adapter, &uuid, svc_size);
	if (start_handle == 0) {
		error("Not enough free handles to register service");
		return;
	}

	DBG("start_handle=0x%04x", start_handle);

	h = start_handle;

	/* Primary service definition */
	bt_uuid16_create(&uuid, GATT_PRIM_SVC_UUID);
	att_put_u16(TX_POWER_SVC_UUID, &atval[0]);
	attrib_db_add(adapter, h++, &uuid, ATT_NONE, ATT_NOT_PERMITTED, atval, 2);

	/* Power level characteristic */
	bt_uuid16_create(&uuid, GATT_CHARAC_UUID);
	atval[0] = ATT_CHAR_PROPER_READ | ATT_CHAR_PROPER_NOTIFY;
	att_put_u16(h + 1, &atval[1]);
	att_put_u16(POWER_LEVEL_CHR_UUID, &atval[3]);
	attrib_db_add(adapter, h++, &uuid, ATT_NONE, ATT_NOT_PERMITTED, atval, 5);

	/* Power level value */
	bt_uuid16_create(&uuid, POWER_LEVEL_CHR_UUID);
	att_put_u8(0x00, &atval[0]);
	attrib_db_add(adapter, h++, &uuid, ATT_NONE, ATT_NOT_PERMITTED, atval, 1);

	/* Client characteristic configuration */
	bt_uuid16_create(&uuid, GATT_CLIENT_CHARAC_CFG_UUID);
	atval[0] = 0x00;
	atval[1] = 0x00;
	attrib_db_add(adapter, h++, &uuid, ATT_NONE, ATT_NONE, atval, 2);

	g_assert(h - start_handle == svc_size);
}

static DBusMessage *get_properties(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	DBusMessageIter iter;
	DBusMessageIter dict;
	DBusMessage *reply = NULL;
	const char *linkloss_level, *immalert_level;
	struct btd_device *device = data;

	reply = dbus_message_new_method_return(msg);
	if (!reply)
		return NULL;

	linkloss_level = link_loss_get_alert_level(device);
	immalert_level = imm_alert_get_level(device);

	dbus_message_iter_init_append(reply, &iter);

	if (!dbus_message_iter_open_container(&iter, DBUS_TYPE_ARRAY,
			DBUS_DICT_ENTRY_BEGIN_CHAR_AS_STRING
			DBUS_TYPE_STRING_AS_STRING DBUS_TYPE_VARIANT_AS_STRING
			DBUS_DICT_ENTRY_END_CHAR_AS_STRING, &dict))
		goto err;

	dict_append_entry(&dict, "LinkLossAlertLevel", DBUS_TYPE_STRING,
							&linkloss_level);
	dict_append_entry(&dict, "ImmediateAlertLevel", DBUS_TYPE_STRING,
							&immalert_level);

	if (!dbus_message_iter_close_container(&iter, &dict))
		goto err;

	return reply;

err:
	if (reply)
		dbus_message_unref(reply);
	return btd_error_failed(msg, "not enough memory");
}

static const GDBusMethodTable reporter_methods[] = {
	{ GDBUS_METHOD("GetProperties",
			NULL, GDBUS_ARGS({ "properties", "a{sv}" }),
			get_properties) },
	{ }
};

static const GDBusSignalTable reporter_signals[] = {
	{ GDBUS_SIGNAL("PropertyChanged",
			GDBUS_ARGS({ "name", "s" }, { "value", "v" })) },
	{ }
};

static void unregister_reporter_device(gpointer data, gpointer user_data)
{
	struct btd_device *device = data;
	struct reporter_adapter *radapter = user_data;
	const char *path = device_get_path(device);

	DBG("unregister on device %s", path);

	g_dbus_unregister_interface(radapter->conn, path,
					PROXIMITY_REPORTER_INTERFACE);

	radapter->devices = g_slist_remove(radapter->devices, device);
	btd_device_unref(device);
}

static void register_reporter_device(struct btd_device *device,
					struct reporter_adapter *radapter)
{
	const char *path = device_get_path(device);

	DBG("register on device %s", path);

	g_dbus_register_interface(radapter->conn, path,
					PROXIMITY_REPORTER_INTERFACE,
					reporter_methods, reporter_signals,
					NULL, device, NULL);

	btd_device_ref(device);
	radapter->devices = g_slist_prepend(radapter->devices, device);
}

static int reporter_device_probe(struct btd_device *device, GSList *uuids)
{
	struct reporter_adapter *radapter;
	struct btd_adapter *adapter = device_get_adapter(device);

	radapter = find_reporter_adapter(adapter);
	if (!radapter)
		return -1;

	register_reporter_device(device, radapter);
	return 0;
}

static void reporter_device_remove(struct btd_device *device)
{
	struct reporter_adapter *radapter;
	struct btd_adapter *adapter = device_get_adapter(device);

	radapter = find_reporter_adapter(adapter);
	if (!radapter)
		return;

	unregister_reporter_device(device, radapter);
}

/* device driver for tracking remote GATT client devices */
static struct btd_device_driver reporter_device_driver = {
	.name = "Proximity GATT Reporter Device Tracker Driver",
	.uuids = BTD_UUIDS(GATT_UUID),
	.probe = reporter_device_probe,
	.remove = reporter_device_remove,
};

int reporter_init(struct btd_adapter *adapter)
{
	struct reporter_adapter *radapter;
	DBusConnection *conn;

	if (!main_opts.gatt_enabled) {
		DBG("GATT is disabled");
		return -ENOTSUP;
	}

	conn = dbus_bus_get(DBUS_BUS_SYSTEM, NULL);
	if (!conn)
		return -1;

	radapter = g_new0(struct reporter_adapter, 1);
	radapter->adapter = adapter;
	radapter->conn = conn;

	link_loss_register(adapter, radapter->conn);
	register_tx_power(adapter);
	imm_alert_register(adapter, radapter->conn);

	btd_register_device_driver(&reporter_device_driver);

	reporter_adapters = g_slist_prepend(reporter_adapters, radapter);
	DBG("Proximity Reporter for adapter %p", adapter);

	return 0;
}

void reporter_exit(struct btd_adapter *adapter)
{
	struct reporter_adapter *radapter = find_reporter_adapter(adapter);
	if (!radapter)
		return;

	btd_unregister_device_driver(&reporter_device_driver);

	g_slist_foreach(radapter->devices, unregister_reporter_device,
								radapter);

	link_loss_unregister(adapter);
	imm_alert_unregister(adapter);
	dbus_connection_unref(radapter->conn);

	reporter_adapters = g_slist_remove(reporter_adapters, radapter);
	g_free(radapter);
}
