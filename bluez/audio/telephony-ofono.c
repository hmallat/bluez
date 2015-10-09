/*
 *
 *  BlueZ - Bluetooth protocol stack for Linux
 *
 *  Copyright (C) 2009-2010  Intel Corporation
 *  Copyright (C) 2006-2009  Nokia Corporation
 *  Copyright (C) 2004-2010  Marcel Holtmann <marcel@holtmann.org>
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

#define _GNU_SOURCE

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <glib.h>
#include <glib-unix.h>
#include <dbus/dbus.h>
#include <gdbus.h>

#include <bluetooth/sdp.h>

#include "log.h"
#include "telephony.h"
#include "main.h"

enum net_registration_status {
	NETWORK_REG_STATUS_HOME = 0x00,
	NETWORK_REG_STATUS_ROAM,
	NETWORK_REG_STATUS_NOSERV
};

struct voice_call {
	char *obj_path;
	char *vcmanager_path;
	int status;
	gboolean originating;
	gboolean conference;
	char *number;
	guint watch;

	gboolean status_pending;
	gboolean waiting_for_answer;
	gchar *hold_dial_clir;
	gchar *hold_dial_number;
};

struct dial {
	gchar *hold_dial_clir;
	gchar *hold_dial_number;
	char *vcmanager_path;
};

static DBusConnection *connection = NULL;
static char *modem_obj_path = NULL;
static char *last_dialed_number = NULL;
static gchar *last_dialed_number_path = NULL;
static GSList *calls = NULL;
static GSList *watches = NULL;
static GSList *pending = NULL;

#define OFONO_BUS_NAME "org.ofono"
#define OFONO_PATH "/"
#define OFONO_MODEM_INTERFACE "org.ofono.Modem"
#define OFONO_MANAGER_INTERFACE "org.ofono.Manager"
#define OFONO_NETWORKREG_INTERFACE "org.ofono.NetworkRegistration"
#define OFONO_VCMANAGER_INTERFACE "org.ofono.VoiceCallManager"
#define OFONO_VC_INTERFACE "org.ofono.VoiceCall"

/* HAL battery namespace key values */
static int battchg_cur = -1;    /* "battery.charge_level.current" */
static int battchg_last = -1;   /* "battery.charge_level.last_full" */
static int battchg_design = -1; /* "battery.charge_level.design" */

static struct {
	uint8_t status;
	uint32_t signals_bar;
	char *operator_name;
} net = {
	.status = NETWORK_REG_STATUS_NOSERV,
	.signals_bar = 0,
	.operator_name = NULL,
};

static char *subscriber_number = NULL;

static gboolean events_enabled = FALSE;

static guint statefs_batt_watch = 0;
static int statefs_batt_fd = -1;

static uint32_t telephony_features = 0;
static uint32_t telephony_supp_features = 0;

static struct indicator ofono_indicators[] =
{
	{ "battchg",	"0-5",	5,	TRUE },
	{ "signal",	"0-5",	5,	TRUE },
	{ "service",	"0,1",	1,	TRUE },
	{ "call",	"0,1",	0,	TRUE },
	{ "callsetup",	"0-3",	0,	TRUE },
	{ "callheld",	"0-2",	0,	FALSE },
	{ "roam",	"0,1",	0,	TRUE },
	{ NULL }
};

static void update_call_status(void);

static struct voice_call *nth_call_at(const char *vcmanager_path,
					int n)
{
	int count = 0;
	GSList *l;

	DBG("%s[%d]", vcmanager_path, n);

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *vc = l->data;
		if (!g_strcmp0(vcmanager_path, vc->vcmanager_path)) {
			if (n == count)
				return vc;
			count++;
		}
	}

	return NULL;
}

/* Voicecall manager which is the target of call management (placing
   calls on hold, swapping active and held calls, multiparty call
   management) */
static const char *active_vcmanager_path(void)
{
	DBG("%s", modem_obj_path);
	return modem_obj_path;
}

/* Voicecall manager which is preferred for establishing new calls
   (can be the same as active vcamanager) */
static const char *preferred_vcmanager_path(void)
{
	DBG("%s", modem_obj_path);
	return modem_obj_path;
}

static gboolean known_vcmanager_path(const char *vcmanager_path)
{
	return (!modem_obj_path || g_strcmp0(vcmanager_path, modem_obj_path))
		? FALSE
		: TRUE;
}

static void waiting_for_answer_clear(struct voice_call *vc)
{
	DBG("");
	vc->waiting_for_answer = FALSE;
}

static void waiting_for_answer_set(struct voice_call *vc)
{
	DBG("");
	vc->waiting_for_answer = TRUE;
}

static gboolean waiting_for_answer_is_set(struct voice_call *vc)
{
	DBG("%s", vc->waiting_for_answer ? "TRUE" : "FALSE");
	return vc->waiting_for_answer;
}

static void status_clear(struct voice_call *vc)
{
	vc->status_pending = FALSE;
}

static void status_set_all(const char *vcmanager_path)
{
	GSList *l;

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *vc = l->data;
		if (!g_strcmp0(vcmanager_path, vc->vcmanager_path))
			vc->status_pending = TRUE;
	}
}

static gboolean status_pending(void)
{
	GSList *l;

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *vc = l->data;
		if (vc->status_pending == TRUE)
			return TRUE;
	}

	return FALSE;
}

static struct voice_call *find_vc(const char *path)
{
	GSList *l;

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *vc = l->data;

		if (g_str_equal(vc->obj_path, path))
			return vc;
	}

	return NULL;
}

static struct voice_call *find_vc_with_status(int status)
{
	GSList *l;

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *vc = l->data;

		if (vc->status == status)
			return vc;
	}

	return NULL;
}

static struct voice_call *find_vc_with_status_at(const char *vcmanager_path,
							int status)
{
	GSList *l;

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *vc = l->data;

		if (!g_strcmp0(vcmanager_path, vc->vcmanager_path) &&
				vc->status == status)
			return vc;
	}

	return NULL;
}

static struct voice_call *find_vc_without_status(int status)
{
	GSList *l;

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *call = l->data;

		if (call->status != status)
			return call;
	}

	return NULL;
}

static int number_type(const char *number)
{
	if (number == NULL)
		return NUMBER_TYPE_TELEPHONY;

	if (number[0] == '+' || strncmp(number, "00", 2) == 0)
		return NUMBER_TYPE_INTERNATIONAL;

	return NUMBER_TYPE_TELEPHONY;
}

void telephony_device_connected(void *telephony_device)
{
	struct voice_call *coming;

	DBG("telephony-ofono: device %p connected", telephony_device);

	coming = find_vc_with_status(CALL_STATUS_INCOMING);
	if (coming) {
		if (find_vc_with_status(CALL_STATUS_ACTIVE))
			telephony_call_waiting_ind(coming->number,
						number_type(coming->number));
		else
			telephony_incoming_call_ind(coming->number,
						number_type(coming->number),
						FALSE);
	}
}

void telephony_device_disconnected(void *telephony_device)
{
	DBG("telephony-ofono: device %p disconnected", telephony_device);
	events_enabled = FALSE;
}

void telephony_event_reporting_req(void *telephony_device, int ind)
{
	events_enabled = ind == 1 ? TRUE : FALSE;

	telephony_event_reporting_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_response_and_hold_req(void *telephony_device, int rh)
{
	telephony_response_and_hold_rsp(telephony_device,
						CME_ERROR_NOT_SUPPORTED);
}

void telephony_last_dialed_number_req(void *telephony_device)
{
	DBG("telephony-ofono: last dialed number request");

	/* If a path is given, prefer that to the number spied from
	   ofono signals */
	if (last_dialed_number_path != NULL) {
		gchar *buf = NULL;
		GError *err = NULL;

		if (g_file_get_contents(last_dialed_number_path,
						&buf, NULL, &err)) {
			DBG("Dialing last dialed number '%s'", buf);
			telephony_dial_number_req(telephony_device, buf);
			g_free(buf);
		} else {
			DBG("Failed to read last dialed number from '%s': %s",
				last_dialed_number_path, err->message);
			telephony_last_dialed_number_rsp(telephony_device,
							CME_ERROR_NOT_ALLOWED);
			g_error_free(err);
		}

	} else {
		if (last_dialed_number)
			telephony_dial_number_req(telephony_device,
						last_dialed_number);
		else
			telephony_last_dialed_number_rsp(telephony_device,
							CME_ERROR_NOT_ALLOWED);
	}

}

static int send_method_call(const char *dest, const char *path,
                                const char *interface, const char *method,
                                DBusPendingCallNotifyFunction cb,
                                void *user_data, int type, ...)
{
	DBusMessage *msg;
	DBusPendingCall *call;
	va_list args;

	msg = dbus_message_new_method_call(dest, path, interface, method);
	if (!msg) {
		error("Unable to allocate new D-Bus %s message", method);
		return -ENOMEM;
	}

	va_start(args, type);

	if (!dbus_message_append_args_valist(msg, type, args)) {
		dbus_message_unref(msg);
		va_end(args);
		return -EIO;
	}

	va_end(args);

	if (!cb) {
		g_dbus_send_message(connection, msg);
		return 0;
	}

	if (!dbus_connection_send_with_reply(connection, msg, &call, -1)) {
		error("Sending %s failed", method);
		dbus_message_unref(msg);
		return -EIO;
	}

	dbus_pending_call_set_notify(call, cb, user_data, NULL);
	pending = g_slist_prepend(pending, call);
	dbus_message_unref(msg);

	return 0;
}

static int answer_call(struct voice_call *vc)
{
	DBG("%s", vc->number);
	DBG("%s", vc->obj_path);
	return send_method_call(OFONO_BUS_NAME, vc->obj_path,
						OFONO_VC_INTERFACE, "Answer",
						NULL, NULL, DBUS_TYPE_INVALID);
}

static int release_call(struct voice_call *vc)
{
	DBG("%s", vc->number);
	DBG("%s", vc->obj_path);
	return send_method_call(OFONO_BUS_NAME, vc->obj_path,
						OFONO_VC_INTERFACE, "Hangup",
						NULL, NULL, DBUS_TYPE_INVALID);
}

static void answer_waiting_call(void)
{
	GSList *l;

	DBG("");

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *vc = l->data;
		if (waiting_for_answer_is_set(vc) == TRUE) {
			answer_call(vc);
			break;
		}
	}
}

static int release_answer_calls(const char *vcmanager_path)
{
	struct voice_call *active = NULL;
	struct voice_call *waiting = NULL;

	DBG("%s", vcmanager_path);

	active = find_vc_with_status_at(vcmanager_path, CALL_STATUS_ACTIVE);
	waiting = find_vc_with_status_at(vcmanager_path, CALL_STATUS_WAITING);
	if (active == NULL || waiting == NULL)
		return -EIO;

	/* Answer this call when the current call has disconnected */
	waiting_for_answer_set(waiting);

	return send_method_call(OFONO_BUS_NAME, active->obj_path,
						OFONO_VC_INTERFACE, "Hangup",
						NULL, NULL,
						DBUS_TYPE_INVALID);
}

static int release_swap_calls(const char *vcmanager_path)
{
	DBG("%s", vcmanager_path);
	return send_method_call(OFONO_BUS_NAME, vcmanager_path,
						OFONO_VCMANAGER_INTERFACE,
						"ReleaseAndSwap",
						NULL, NULL, DBUS_TYPE_INVALID);
}

static int hold_answer_calls(const char *vcmanager_path)
{
	DBG("%s", vcmanager_path);
	return send_method_call(OFONO_BUS_NAME, vcmanager_path,
						OFONO_VCMANAGER_INTERFACE,
						"HoldAndAnswer",
						NULL, NULL, DBUS_TYPE_INVALID);
}

static int split_call(struct voice_call *call)
{
	DBG("%s", call->vcmanager_path);
	DBG("%s", call->number);
	DBG("%s", call->obj_path);
	return send_method_call(OFONO_BUS_NAME, call->vcmanager_path,
						OFONO_VCMANAGER_INTERFACE,
						"PrivateChat",
						NULL, NULL,
						DBUS_TYPE_OBJECT_PATH,
						&call->obj_path,
						DBUS_TYPE_INVALID);
	return -1;
}

static int swap_calls(const char *vcmanager_path)
{
	DBG("%s", vcmanager_path);
	return send_method_call(OFONO_BUS_NAME, vcmanager_path,
						OFONO_VCMANAGER_INTERFACE,
						"SwapCalls",
						NULL, NULL, DBUS_TYPE_INVALID);
}

static int create_conference(const char *vcmanager_path)
{
	DBG("%s", vcmanager_path);
	return send_method_call(OFONO_BUS_NAME, vcmanager_path,
						OFONO_VCMANAGER_INTERFACE,
						"CreateMultiparty",
						NULL, NULL, DBUS_TYPE_INVALID);
}

static int release_conference(const char *vcmanager_path)
{
	DBG("%s", vcmanager_path);
	return send_method_call(OFONO_BUS_NAME, vcmanager_path,
						OFONO_VCMANAGER_INTERFACE,
						"HangupMultiparty",
						NULL, NULL, DBUS_TYPE_INVALID);
}

static int call_transfer(const char *vcmanager_path)
{
	DBG("%s", vcmanager_path);
	return send_method_call(OFONO_BUS_NAME, vcmanager_path,
						OFONO_VCMANAGER_INTERFACE,
						"Transfer",
						NULL, NULL, DBUS_TYPE_INVALID);
}

void telephony_terminate_call_req(void *telephony_device)
{
	struct voice_call *call;
	struct voice_call *alerting;
	int err;

	call = find_vc_with_status(CALL_STATUS_ACTIVE);
	if (!call)
		call = calls ? calls->data : NULL;

	if (!call) {
		error("No active call");
		telephony_terminate_call_rsp(telephony_device,
						CME_ERROR_NOT_ALLOWED);
		return;
	}

	alerting = find_vc_with_status(CALL_STATUS_ALERTING);
	if (call->status == CALL_STATUS_HELD && alerting)
		err = release_call(alerting);
	else if (call->conference)
		err = release_conference(call->vcmanager_path);
	else
		err = release_call(call);

	if (err < 0)
		telephony_terminate_call_rsp(telephony_device,
						CME_ERROR_AG_FAILURE);
	else
		telephony_terminate_call_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_answer_call_req(void *telephony_device)
{
	struct voice_call *vc;
	int ret;

	vc = find_vc_with_status(CALL_STATUS_INCOMING);
	if (!vc)
		vc = find_vc_with_status(CALL_STATUS_ALERTING);

	if (!vc)
		vc = find_vc_with_status(CALL_STATUS_WAITING);

	if (!vc) {
		telephony_answer_call_rsp(telephony_device,
					CME_ERROR_NOT_ALLOWED);
		return;
	}

	ret = answer_call(vc);
	if (ret < 0) {
		telephony_answer_call_rsp(telephony_device,
					CME_ERROR_AG_FAILURE);
		return;
	}

	telephony_answer_call_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_dial_number_req(void *telephony_device, const char *number)
{
	struct voice_call *vc = NULL;
	const char *clir;
	int ret;

	DBG("telephony-ofono: dial request to %s", number);

	if (!preferred_vcmanager_path()) {
		telephony_dial_number_rsp(telephony_device,
					CME_ERROR_AG_FAILURE);
		return;
	}

	if(!number || *number == '\0') {
		telephony_dial_number_rsp(telephony_device,
					CME_ERROR_AG_FAILURE);
		return;
	}

	/* Fake memory dialing for memory location one. */
	if (!strcmp(number, ">1")) {
		telephony_last_dialed_number_req(telephony_device);
		return;
	}

	/* Block other memory dialing; more proper would be to wait for
	   ofono D-Bus reply, but I think that'd need audio device
	   refcounting so that it doesn't potentially disappear while
	   we wait for D-Bus reply. */
	if (*number == '>') {
		telephony_dial_number_rsp(telephony_device,
					CME_ERROR_AG_FAILURE);
		return;
	}

	if (!strncmp(number, "*31#", 4)) {
		number += 4;
		clir = "enabled";
	} else if (!strncmp(number, "#31#", 4)) {
		number += 4;
		clir =  "disabled";
	} else
		clir = "default";

	vc = find_vc_with_status(CALL_STATUS_ACTIVE);
	if (vc != NULL && g_slist_length(calls) == 1) {
		DBG("Explicitly holding current call before dialing");
		g_free(vc->hold_dial_number);
		vc->hold_dial_number = g_strdup(number);
		g_free(vc->hold_dial_clir);
		vc->hold_dial_clir = g_strdup(clir);
		if (swap_calls(vc->vcmanager_path) != 0)
			telephony_dial_number_rsp(telephony_device,
						CME_ERROR_AG_FAILURE);
		else
			telephony_dial_number_rsp(telephony_device,
						CME_ERROR_NONE);
		return;
	}

	ret = send_method_call(OFONO_BUS_NAME, preferred_vcmanager_path(),
			OFONO_VCMANAGER_INTERFACE,
                        "Dial", NULL, NULL,
			DBUS_TYPE_STRING, &number,
			DBUS_TYPE_STRING, &clir,
			DBUS_TYPE_INVALID);

	if (ret < 0)
		telephony_dial_number_rsp(telephony_device,
			CME_ERROR_AG_FAILURE);
	else
		telephony_dial_number_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_transmit_dtmf_req(void *telephony_device, char tone)
{
	char *tone_string;
	int ret;

	DBG("telephony-ofono: transmit dtmf: %c", tone);

	if (!preferred_vcmanager_path()) {
		telephony_transmit_dtmf_rsp(telephony_device,
					CME_ERROR_AG_FAILURE);
		return;
	}

	tone_string = g_strdup_printf("%c", tone);
	ret = send_method_call(OFONO_BUS_NAME, preferred_vcmanager_path(),
			OFONO_VCMANAGER_INTERFACE,
			"SendTones", NULL, NULL,
			DBUS_TYPE_STRING, &tone_string,
			DBUS_TYPE_INVALID);
	g_free(tone_string);

	if (ret < 0)
		telephony_transmit_dtmf_rsp(telephony_device,
			CME_ERROR_AG_FAILURE);
	else
		telephony_transmit_dtmf_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_subscriber_number_req(void *telephony_device)
{
	DBG("telephony-ofono: subscriber number request");

	if (subscriber_number)
		telephony_subscriber_number_ind(subscriber_number,
						NUMBER_TYPE_TELEPHONY,
						SUBSCRIBER_SERVICE_VOICE);
	telephony_subscriber_number_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_list_current_calls_req(void *telephony_device)
{
	GSList *l;
	int i;

	DBG("telephony-ofono: list current calls request");

	for (l = calls, i = 1; l != NULL; l = l->next, i++) {
		struct voice_call *vc = l->data;
		int direction, multiparty;

		direction = vc->originating ?
				CALL_DIR_OUTGOING : CALL_DIR_INCOMING;

		multiparty = vc->conference ?
				CALL_MULTIPARTY_YES : CALL_MULTIPARTY_NO;

		DBG("call %s direction %d multiparty %d", vc->number,
							direction, multiparty);

		telephony_list_current_call_ind(i, direction, vc->status,
					CALL_MODE_VOICE, multiparty,
					vc->number, number_type(vc->number));
	}

	telephony_list_current_calls_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_operator_selection_req(void *telephony_device)
{
	DBG("telephony-ofono: operator selection request");

	telephony_operator_selection_ind(OPERATOR_MODE_AUTO,
				net.operator_name ? net.operator_name : "");
	telephony_operator_selection_rsp(telephony_device, CME_ERROR_NONE);
}

static void foreach_vc_with_status(int status,
					int (*func)(struct voice_call *vc))
{
	GSList *l;

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *call = l->data;

		if (call->status == status)
			func(call);
	}
}

static void foreach_vc_with_status_at(const char *vcmanager_path,
					int status,
					int (*func)(struct voice_call *vc))
{
	GSList *l;

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *call = l->data;

		if (!g_strcmp0(vcmanager_path, call->vcmanager_path) &&
				call->status == status)
			func(call);
	}
}

static cme_error_t chld0(const char *vcmanager_path)
{
	/* HFP 1.5 documentation on AT+CHLD:

	   "0 = Releases all held calls or sets User Determined User
	   Busy (UDUB) for a waiting call."

	*/

	if (find_vc_with_status_at(vcmanager_path, CALL_STATUS_WAITING))
		foreach_vc_with_status_at(vcmanager_path,
						CALL_STATUS_WAITING,
						release_call);
	else
		foreach_vc_with_status_at(vcmanager_path,
						CALL_STATUS_HELD,
						release_call);

	return 0;
}

static cme_error_t chld1(const char *vcmanager_path, struct voice_call *call)
{
	/* HFP 1.5 documentation on AT+CHLD:

	   "1 = Releases all active calls (if any exist) and accepts
	   the other (held or waiting) call.

	   1<idx> = Releases specified active call only (<idx>)."

	*/

	if (call) {
		if (release_call(call) != 0)
			return CME_ERROR_AG_FAILURE;
	} else {
		call = find_vc_with_status_at(vcmanager_path,
						CALL_STATUS_WAITING);
		if (call) {
			if (release_answer_calls(vcmanager_path) != 0)
				return CME_ERROR_AG_FAILURE;
		} else {
			if (release_swap_calls(vcmanager_path) != 0)
				return CME_ERROR_AG_FAILURE;
		}
	}

	return 0;
}

static cme_error_t chld2(const char *vcmanager_path, struct voice_call *call)
{
	/* HFP 1.5 documentation on AT+CHLD:

	   "2 = Places all active calls (if any exist) on hold and accepts
	   the other (held or waiting) call.

	   2<idx> = Request private consultation mode with specified
	   call (<idx>).  (Place all calls on hold EXCEPT the call
	   indicated by <idx>.)"

	*/

	if (call) {
		if (split_call(call) != 0)
			return CME_ERROR_AG_FAILURE;
	} else {
		call = find_vc_with_status_at(vcmanager_path,
						CALL_STATUS_WAITING);

		if (call) {
			if (hold_answer_calls(vcmanager_path) != 0)
				return CME_ERROR_AG_FAILURE;
		} else {
			if (swap_calls(vcmanager_path) != 0)
				return CME_ERROR_AG_FAILURE;
		}
	}

	return 0;
}

static cme_error_t chld3(const char *vcmanager_path)
{
	/* HFP 1.5 documentation on AT+CHLD:

	   "3 = Adds a held call to the conversation."

	*/

	if (!(telephony_supp_features & AG_FEATURE_SUPP_CONF_CALL))
		return CME_ERROR_NOT_SUPPORTED;

	if (find_vc_with_status_at(vcmanager_path, CALL_STATUS_HELD) ||
		find_vc_with_status_at(vcmanager_path, CALL_STATUS_WAITING)) {
		if (create_conference(vcmanager_path) != 0)
			return CME_ERROR_AG_FAILURE;
	} else {
		return CME_ERROR_NOT_ALLOWED;
	}

	return 0;
}

static cme_error_t chld4(const char *vcmanager_path)
{
	/* HFP 1.5 documentation on AT+CHLD:

	   "Connects the two calls and disconnects the subscriber from
	   both calls (Explicit Call Transfer)."

	*/

	if (!(telephony_supp_features & AG_FEATURE_SUPP_CONF_CALL))
		return CME_ERROR_NOT_SUPPORTED;

	if (find_vc_with_status_at(vcmanager_path, CALL_STATUS_HELD) ||
		find_vc_with_status_at(vcmanager_path, CALL_STATUS_WAITING)) {
		if (call_transfer(vcmanager_path) != 0)
			return CME_ERROR_AG_FAILURE;
	} else {
		return CME_ERROR_NOT_ALLOWED;
	}

	return 0;
}

void telephony_call_hold_req(void *telephony_device, const char *cmd)
{
	const char *idx = NULL;
	struct voice_call *call = NULL;
	cme_error_t cme_err = CME_ERROR_NONE;
	const char *vcmanager_path = NULL;

	DBG("telephony-ofono: got call hold request %s", cmd);

	vcmanager_path = active_vcmanager_path();
	if (!vcmanager_path) {
		cme_err = CME_ERROR_AG_FAILURE;
		goto done;
	}

	if (!(telephony_features & AG_FEATURE_THREE_WAY_CALLING)) {
		cme_err = CME_ERROR_NOT_SUPPORTED;
		goto done;
	}

	if (strlen(cmd) > 1) {
		if (cmd[0] != '1' && cmd[0] != '2') {
			cme_err = CME_ERROR_NOT_SUPPORTED;
			goto done;
		}

		if (telephony_features & AG_FEATURE_ENHANCED_CALL_CONTROL) {
			idx = &cmd[1];
		} else {
			cme_err = CME_ERROR_NOT_SUPPORTED;
			goto done;
		}
	} else
		idx = NULL;

	if (idx) {
		call = nth_call_at(vcmanager_path, strtol(idx, NULL, 0) - 1);
		if (call == NULL) {
			cme_err = CME_ERROR_INVALID_INDEX;
			goto done;
		}
	} else
		call = NULL;

	switch (cmd[0]) {
	case '0':
		cme_err = chld0(vcmanager_path);
		break;
	case '1':
		cme_err = chld1(vcmanager_path, call);
		break;
	case '2':
		cme_err = chld2(vcmanager_path, call);
		break;
	case '3':
		cme_err = chld3(vcmanager_path);
		break;
	case '4':
		cme_err = chld4(vcmanager_path);
		break;
	default:
		DBG("Unknown call hold request");
		cme_err = CME_ERROR_NOT_SUPPORTED;
		break;
	}

done:
	if (cme_err == CME_ERROR_NONE) /* wait for all call statuses now */
		status_set_all(vcmanager_path);

	telephony_call_hold_rsp(telephony_device, cme_err);
}

void telephony_nr_and_ec_req(void *telephony_device, gboolean enable)
{
	DBG("telephony-ofono: got %s NR and EC request",
			enable ? "enable" : "disable");

	telephony_nr_and_ec_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_key_press_req(void *telephony_device, const char *keys)
{
	struct voice_call *active, *incoming;
	int err;

	DBG("telephony-ofono: got key press request for %s", keys);

	incoming = find_vc_with_status(CALL_STATUS_INCOMING);

	active = find_vc_with_status(CALL_STATUS_ACTIVE);

	if (incoming)
		err = answer_call(incoming);
	else if (active)
		err = release_call(active);
	else
		err = 0;

	if (err < 0)
		telephony_key_press_rsp(telephony_device,
							CME_ERROR_AG_FAILURE);
	else
		telephony_key_press_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_voice_dial_req(void *telephony_device, gboolean enable)
{
	DBG("telephony-ofono: got %s voice dial request",
			enable ? "enable" : "disable");

	telephony_voice_dial_rsp(telephony_device, CME_ERROR_NOT_SUPPORTED);
}

static gboolean iter_get_basic_args(DBusMessageIter *iter,
					int first_arg_type, ...)
{
	int type;
	va_list ap;

	va_start(ap, first_arg_type);

	for (type = first_arg_type; type != DBUS_TYPE_INVALID;
		type = va_arg(ap, int)) {
		void *value = va_arg(ap, void *);
		int real_type = dbus_message_iter_get_arg_type(iter);

		if (real_type != type) {
			error("iter_get_basic_args: expected %c but got %c",
				(char) type, (char) real_type);
			break;
		}

		dbus_message_iter_get_basic(iter, value);
		dbus_message_iter_next(iter);
	}

	va_end(ap);

	return type == DBUS_TYPE_INVALID ? TRUE : FALSE;
}

static void call_free(void *data)
{
	struct voice_call *vc = data;

	DBG("%s", vc->obj_path);

	update_call_status();
	if (vc->status != CALL_STATUS_ACTIVE)
		telephony_update_indicator(ofono_indicators, "callsetup",
							EV_CALLSETUP_INACTIVE);

	if (vc->status == CALL_STATUS_INCOMING)
		telephony_calling_stopped_ind();

	g_dbus_remove_watch(connection, vc->watch);
	g_free(vc->vcmanager_path);
	g_free(vc->obj_path);
	g_free(vc->number);
	g_free(vc->hold_dial_clir);
	g_free(vc->hold_dial_number);
	memset(vc, 0, sizeof(struct voice_call));
	g_free(vc);
}

static void update_held_status(void)
{
	DBG("");

	if (status_pending()) {
		DBG("Call statuses pending. ");
		return;
	}

	if (find_vc_with_status(CALL_STATUS_HELD)) {
		if (find_vc_without_status(CALL_STATUS_HELD))
			telephony_update_indicator(ofono_indicators,
						"callheld",
						EV_CALLHELD_MULTIPLE);
		else
			telephony_update_indicator(ofono_indicators,
						"callheld",
						EV_CALLHELD_ON_HOLD);
	} else {
		telephony_update_indicator(ofono_indicators,
					"callheld",
					EV_CALLHELD_NONE);
	}
}

static void update_call_status(void)
{
	DBG("");

	if (status_pending()) {
		DBG("Call statuses pending. ");
		return;
	}

	if (find_vc_with_status(CALL_STATUS_ACTIVE) ||
			find_vc_with_status(CALL_STATUS_HELD)) {
		telephony_update_indicator(ofono_indicators,
					"call",
					EV_CALL_ACTIVE);
	} else {
		telephony_update_indicator(ofono_indicators,
					"call",
					EV_CALL_INACTIVE);
	}
}

static gboolean dial_after_hold(gpointer data)
{
	struct dial *d = (struct dial *)data;
	send_method_call(OFONO_BUS_NAME, d->vcmanager_path,
			OFONO_VCMANAGER_INTERFACE,
			"Dial", NULL, NULL,
			DBUS_TYPE_STRING, &d->hold_dial_number,
			DBUS_TYPE_STRING, &d->hold_dial_clir,
			DBUS_TYPE_INVALID);
	g_free(d->hold_dial_clir);
	g_free(d->hold_dial_number);
	g_free(d->vcmanager_path);
	g_free(d);

	return FALSE;
}

static gboolean handle_vc_property_changed(DBusConnection *conn,
					DBusMessage *msg, void *data)
{
	struct voice_call *vc = data;
	const char *obj_path = dbus_message_get_path(msg);
	DBusMessageIter iter, sub;
	const char *property, *state;

	audio_wakelock_get();

	DBG("path %s", obj_path);

	dbus_message_iter_init(msg, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_STRING) {
		error("Unexpected signature in vc PropertyChanged signal");
		return TRUE;
	}

	dbus_message_iter_get_basic(&iter, &property);
	DBG("property %s", property);

	dbus_message_iter_next(&iter);
	dbus_message_iter_recurse(&iter, &sub);
	if (g_str_equal(property, "State")) {
		dbus_message_iter_get_basic(&sub, &state);
		DBG("State %s", state);
		status_clear(vc);
		if (g_str_equal(state, "disconnected")) {
			calls = g_slist_remove(calls, vc);
			call_free(vc);
			/* Answer waiting call if the disconnect was part
			   of release and answer (AT+CHLD=1) processing */
			answer_waiting_call();
		} else if (g_str_equal(state, "active")) {
			if (vc->status == CALL_STATUS_INCOMING)
				telephony_calling_stopped_ind();
			vc->status = CALL_STATUS_ACTIVE;
			update_call_status();
			telephony_update_indicator(ofono_indicators,
							"callsetup",
							EV_CALLSETUP_INACTIVE);
		} else if (g_str_equal(state, "alerting")) {
			telephony_update_indicator(ofono_indicators,
					"callsetup", EV_CALLSETUP_ALERTING);
			vc->status = CALL_STATUS_ALERTING;
			vc->originating = TRUE;
		} else if (g_str_equal(state, "incoming")) {
			/* state change from waiting to incoming */
			telephony_update_indicator(ofono_indicators,
					"callsetup", EV_CALLSETUP_INCOMING);
			telephony_incoming_call_ind(vc->number,
						NUMBER_TYPE_TELEPHONY,
						waiting_for_answer_is_set(vc));
			waiting_for_answer_clear(vc);
			vc->status = CALL_STATUS_INCOMING;
			vc->originating = FALSE;
		} else if (g_str_equal(state, "held")) {
			vc->status = CALL_STATUS_HELD;
			/* in case we have pending dial, do it now */
			if (vc->hold_dial_number != NULL) {
				struct dial *d = NULL;
				d = g_new0(struct dial, 1);
				d->hold_dial_clir = vc->hold_dial_clir;
				d->hold_dial_number = vc->hold_dial_number;
				vc->hold_dial_clir = NULL;
				vc->hold_dial_number = NULL;
				d->vcmanager_path =
					g_strdup(vc->vcmanager_path);
				g_timeout_add_seconds(1, dial_after_hold, d);
			}
		}
		update_held_status();
	} else if (g_str_equal(property, "Multiparty")) {
		dbus_bool_t multiparty;

		dbus_message_iter_get_basic(&sub, &multiparty);
		DBG("Multiparty %s", multiparty ? "True" : "False");
		vc->conference = multiparty;
	}

	return TRUE;
}

static struct voice_call *call_new(const char *path, const char *vcmanager_path, DBusMessageIter *properties)
{
	struct voice_call *vc;

	DBG("%s", path);
	DBG("%s", vcmanager_path);

	vc = g_new0(struct voice_call, 1);
	vc->obj_path = g_strdup(path);
	vc->vcmanager_path = g_strdup(vcmanager_path);
	vc->watch = g_dbus_add_signal_watch(connection, NULL, path,
					OFONO_VC_INTERFACE, "PropertyChanged",
					handle_vc_property_changed, vc, NULL);

	while (dbus_message_iter_get_arg_type(properties)
						== DBUS_TYPE_DICT_ENTRY) {
		DBusMessageIter entry, value;
		const char *property, *cli, *state;
		dbus_bool_t multiparty;

		dbus_message_iter_recurse(properties, &entry);
		dbus_message_iter_get_basic(&entry, &property);

		dbus_message_iter_next(&entry);
		dbus_message_iter_recurse(&entry, &value);

		if (g_str_equal(property, "LineIdentification")) {
			dbus_message_iter_get_basic(&value, &cli);
			DBG("cli %s", cli);
			vc->number = g_strdup(cli);
		} else if (g_str_equal(property, "State")) {
			dbus_message_iter_get_basic(&value, &state);
			DBG("state %s", state);
			if (g_str_equal(state, "incoming"))
				vc->status = CALL_STATUS_INCOMING;
			else if (g_str_equal(state, "dialing"))
				vc->status = CALL_STATUS_DIALING;
			else if (g_str_equal(state, "alerting"))
				vc->status = CALL_STATUS_ALERTING;
			else if (g_str_equal(state, "waiting"))
				vc->status = CALL_STATUS_WAITING;
			else if (g_str_equal(state, "held"))
				vc->status = CALL_STATUS_HELD;
		} else if (g_str_equal(property, "Multiparty")) {
			dbus_message_iter_get_basic(&value, &multiparty);
			DBG("Multipary %s", multiparty ? "True" : "False");
			vc->conference = multiparty;
		}

		dbus_message_iter_next(properties);
	}

	switch (vc->status) {
	case CALL_STATUS_INCOMING:
		DBG("CALL_STATUS_INCOMING");
		vc->originating = FALSE;
		telephony_update_indicator(ofono_indicators, "callsetup",
					EV_CALLSETUP_INCOMING);
		telephony_incoming_call_ind(vc->number, NUMBER_TYPE_TELEPHONY,
			FALSE);
		break;
	case CALL_STATUS_DIALING:
		DBG("CALL_STATUS_DIALING");
		vc->originating = TRUE;
		g_free(last_dialed_number);
		last_dialed_number = g_strdup(vc->number);
		telephony_update_indicator(ofono_indicators, "callsetup",
					EV_CALLSETUP_OUTGOING);
		break;
	case CALL_STATUS_ALERTING:
		DBG("CALL_STATUS_ALERTING");
		vc->originating = TRUE;
		g_free(last_dialed_number);
		last_dialed_number = g_strdup(vc->number);
		telephony_update_indicator(ofono_indicators, "callsetup",
					EV_CALLSETUP_ALERTING);
		break;
	case CALL_STATUS_WAITING:
		DBG("CALL_STATUS_WAITING");
		vc->originating = FALSE;
		telephony_update_indicator(ofono_indicators, "callsetup",
					EV_CALLSETUP_INCOMING);
		telephony_call_waiting_ind(vc->number, NUMBER_TYPE_TELEPHONY);
		break;
	}

	return vc;
}

static void remove_pending(DBusPendingCall *call)
{
	pending = g_slist_remove(pending, call);
	dbus_pending_call_unref(call);
}

static void call_added(const char *path, const char *vcmanager_path,
					DBusMessageIter *properties)
{
	struct voice_call *vc;

	DBG("%s", path);

	vc = find_vc(path);
	if (vc)
		return;

	vc = call_new(path, vcmanager_path, properties);
	calls = g_slist_prepend(calls, vc);
}

static void get_calls_reply(DBusPendingCall *call, void *user_data)
{
	DBusError err;
	DBusMessage *reply;
	DBusMessageIter iter, entry;
	const char *vcmanager_path = NULL;

	DBG("");
	reply = dbus_pending_call_steal_reply(call);
	vcmanager_path = dbus_message_get_path(reply);

	dbus_error_init(&err);
	if (dbus_set_error_from_message(&err, reply)) {
		error("ofono replied with an error: %s, %s",
				err.name, err.message);
		dbus_error_free(&err);
		goto done;
	}

	dbus_message_iter_init(reply, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error("Unexpected signature");
		goto done;
	}

	dbus_message_iter_recurse(&iter, &entry);

	while (dbus_message_iter_get_arg_type(&entry)
						== DBUS_TYPE_STRUCT) {
		const char *path;
		DBusMessageIter value, properties;

		dbus_message_iter_recurse(&entry, &value);
		dbus_message_iter_get_basic(&value, &path);

		dbus_message_iter_next(&value);
		dbus_message_iter_recurse(&value, &properties);

		call_added(path, vcmanager_path, &properties);

		dbus_message_iter_next(&entry);
	}

done:
	dbus_message_unref(reply);
	remove_pending(call);
}

static void handle_network_property(const char *property, DBusMessageIter *variant)
{
	const char *status, *operator;
	DBusBasicValue signals_bar;

	if (g_str_equal(property, "Status")) {
		dbus_message_iter_get_basic(variant, &status);
		DBG("Status is %s", status);
		if (g_str_equal(status, "registered")) {
			net.status = NETWORK_REG_STATUS_HOME;
			telephony_update_indicator(ofono_indicators,
						"roam", EV_ROAM_INACTIVE);
			telephony_update_indicator(ofono_indicators,
						"service", EV_SERVICE_PRESENT);
		} else if (g_str_equal(status, "roaming")) {
			net.status = NETWORK_REG_STATUS_ROAM;
			telephony_update_indicator(ofono_indicators,
						"roam", EV_ROAM_ACTIVE);
			telephony_update_indicator(ofono_indicators,
						"service", EV_SERVICE_PRESENT);
		} else {
			net.status = NETWORK_REG_STATUS_NOSERV;
			telephony_update_indicator(ofono_indicators,
						"roam", EV_ROAM_INACTIVE);
			telephony_update_indicator(ofono_indicators,
						"service", EV_SERVICE_NONE);
		}
	} else if (g_str_equal(property, "Name")) {
		dbus_message_iter_get_basic(variant, &operator);
		DBG("Operator is %s", operator);
		g_free(net.operator_name);
		net.operator_name = g_strdup(operator);
	} else if (g_str_equal(property, "Strength")) {
		dbus_message_iter_get_basic(variant, &signals_bar);
		DBG("Strength is %u", (uint32_t)signals_bar.byt);
		net.signals_bar = (uint32_t)signals_bar.byt;
		telephony_update_indicator(ofono_indicators, "signal",
						(net.signals_bar + 20) / 21);
	}
}

static int parse_network_properties(DBusMessageIter *properties)
{
	int i;

	/* Reset indicators */
	for (i = 0; ofono_indicators[i].desc != NULL; i++) {
		if (g_str_equal(ofono_indicators[i].desc, "battchg"))
			ofono_indicators[i].val = 5;
		else
			ofono_indicators[i].val = 0;
	}

	while (dbus_message_iter_get_arg_type(properties)
						== DBUS_TYPE_DICT_ENTRY) {
		const char *key;
		DBusMessageIter value, entry;

		dbus_message_iter_recurse(properties, &entry);
		dbus_message_iter_get_basic(&entry, &key);

		dbus_message_iter_next(&entry);
		dbus_message_iter_recurse(&entry, &value);

		handle_network_property(key, &value);

		dbus_message_iter_next(properties);
	}

	return 0;
}

static void get_properties_reply(DBusPendingCall *call, void *user_data)
{
	DBusError err;
	DBusMessage *reply;
	DBusMessageIter iter, properties;
	int ret = 0;
	const char *vcmanager_path = (const char *)user_data;

	DBG("");
	reply = dbus_pending_call_steal_reply(call);

	dbus_error_init(&err);
	if (dbus_set_error_from_message(&err, reply)) {
		error("ofono replied with an error: %s, %s",
				err.name, err.message);
		dbus_error_free(&err);
		goto done;
	}

	dbus_message_iter_init(reply, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error("Unexpected signature");
		goto done;
	}

	dbus_message_iter_recurse(&iter, &properties);

	ret = parse_network_properties(&properties);
	if (ret < 0) {
		error("Unable to parse %s.GetProperty reply",
						OFONO_NETWORKREG_INTERFACE);
		goto done;
	}

	ret = send_method_call(OFONO_BUS_NAME, vcmanager_path,
				OFONO_VCMANAGER_INTERFACE, "GetCalls",
				get_calls_reply, NULL, DBUS_TYPE_INVALID);
	if (ret < 0)
		error("Unable to send %s.GetCalls",
						OFONO_VCMANAGER_INTERFACE);

done:
	dbus_message_unref(reply);
	remove_pending(call);
}

static void network_found(const char *path)
{
	int ret;

	DBG("%s", path);

	g_free(modem_obj_path);
	modem_obj_path = g_strdup(path);

	ret = send_method_call(OFONO_BUS_NAME, path,
				OFONO_NETWORKREG_INTERFACE, "GetProperties",
			get_properties_reply, (void *)path, DBUS_TYPE_INVALID);
	if (ret < 0)
		error("Unable to send %s.GetProperties",
						OFONO_NETWORKREG_INTERFACE);
}

static void modem_removed(const char *path)
{
	if (g_strcmp0(modem_obj_path, path) != 0)
		return;

	DBG("%s", path);

	g_slist_free_full(calls, call_free);
	calls = NULL;

	g_free(net.operator_name);
	net.operator_name = NULL;
	net.status = NETWORK_REG_STATUS_NOSERV;
	net.signals_bar = 0;

	g_free(modem_obj_path);
	modem_obj_path = NULL;
}

static void parse_modem_interfaces(const char *path, DBusMessageIter *ifaces)
{
	DBG("%s", path);

	while (dbus_message_iter_get_arg_type(ifaces) == DBUS_TYPE_STRING) {
		const char *iface;

		dbus_message_iter_get_basic(ifaces, &iface);

		if (g_str_equal(iface, OFONO_NETWORKREG_INTERFACE)) {
			network_found(path);
			return;
		}

		dbus_message_iter_next(ifaces);
	}

	modem_removed(path);
}

static void modem_added(const char *path, DBusMessageIter *properties)
{
	if (modem_obj_path != NULL) {
		DBG("Ignoring, modem already exist");
		return;
	}

	DBG("%s", path);

	while (dbus_message_iter_get_arg_type(properties)
						== DBUS_TYPE_DICT_ENTRY) {
		const char *key;
		DBusMessageIter interfaces, value, entry;

		dbus_message_iter_recurse(properties, &entry);
		dbus_message_iter_get_basic(&entry, &key);

		dbus_message_iter_next(&entry);
		dbus_message_iter_recurse(&entry, &value);

		if (strcasecmp(key, "Interfaces") != 0)
			goto next;

		if (dbus_message_iter_get_arg_type(&value)
							!= DBUS_TYPE_ARRAY) {
			error("Invalid Signature");
			return;
		}

		dbus_message_iter_recurse(&value, &interfaces);

		parse_modem_interfaces(path, &interfaces);

		if (modem_obj_path != NULL)
			return;

	next:
		dbus_message_iter_next(properties);
	}
}

static void get_modems_reply(DBusPendingCall *call, void *user_data)
{
	DBusError err;
	DBusMessage *reply;
	DBusMessageIter iter, entry;

	DBG("");
	reply = dbus_pending_call_steal_reply(call);

	dbus_error_init(&err);
	if (dbus_set_error_from_message(&err, reply)) {
		error("ofono replied with an error: %s, %s",
				err.name, err.message);
		dbus_error_free(&err);
		goto done;
	}

	/* Skip modem selection if a modem already exist */
	if (modem_obj_path != NULL)
		goto done;

	dbus_message_iter_init(reply, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error("Unexpected signature");
		goto done;
	}

	dbus_message_iter_recurse(&iter, &entry);

	while (dbus_message_iter_get_arg_type(&entry)
						== DBUS_TYPE_STRUCT) {
		const char *path;
		DBusMessageIter item, properties;

		dbus_message_iter_recurse(&entry, &item);
		dbus_message_iter_get_basic(&item, &path);

		dbus_message_iter_next(&item);
		dbus_message_iter_recurse(&item, &properties);

		modem_added(path, &properties);
		if (modem_obj_path != NULL)
			break;

		dbus_message_iter_next(&entry);
	}

done:
	dbus_message_unref(reply);
	remove_pending(call);
}

static gboolean handle_network_property_changed(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	DBusMessageIter iter, variant;
	const char *property;

	audio_wakelock_get();

	dbus_message_iter_init(msg, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_STRING) {
		error("Unexpected signature in networkregistration"
					" PropertyChanged signal");
		return TRUE;
	}
	dbus_message_iter_get_basic(&iter, &property);
	DBG("in handle_registration_property_changed(),"
					" the property is %s", property);

	dbus_message_iter_next(&iter);
	dbus_message_iter_recurse(&iter, &variant);

	handle_network_property(property, &variant);

	return TRUE;
}

static void handle_modem_property(const char *path, const char *property,
						DBusMessageIter *variant)
{
	DBG("%s", property);

	if (g_str_equal(property, "Interfaces")) {
		DBusMessageIter interfaces;

		if (dbus_message_iter_get_arg_type(variant)
							!= DBUS_TYPE_ARRAY) {
			error("Invalid signature");
			return;
		}

		dbus_message_iter_recurse(variant, &interfaces);
		parse_modem_interfaces(path, &interfaces);
	}
}

static gboolean handle_modem_property_changed(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	DBusMessageIter iter, variant;
	const char *property, *path;

	audio_wakelock_get();

	path = dbus_message_get_path(msg);

	/* Ignore if modem already exist and paths doesn't match */
	if (modem_obj_path != NULL &&
				g_str_equal(path, modem_obj_path) == FALSE)
		return TRUE;

	dbus_message_iter_init(msg, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_STRING) {
		error("Unexpected signature in %s.%s PropertyChanged signal",
					dbus_message_get_interface(msg),
					dbus_message_get_member(msg));
		return TRUE;
	}

	dbus_message_iter_get_basic(&iter, &property);

	dbus_message_iter_next(&iter);
	dbus_message_iter_recurse(&iter, &variant);

	handle_modem_property(path, property, &variant);

	return TRUE;
}

static gboolean handle_vcmanager_call_added(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	DBusMessageIter iter, properties;
	const char *path = NULL;
	const char *vcmanager_path = dbus_message_get_path(msg);

	audio_wakelock_get();

	/* Ignore call if modem path doesn't match */
	if (!known_vcmanager_path(vcmanager_path))
		return TRUE;

	dbus_message_iter_init(msg, &iter);

	if (dbus_message_iter_get_arg_type(&iter)
						!= DBUS_TYPE_OBJECT_PATH) {
		error("Unexpected signature in %s.%s signal",
					dbus_message_get_interface(msg),
					dbus_message_get_member(msg));
		return TRUE;
	}

	dbus_message_iter_get_basic(&iter, &path);
	dbus_message_iter_next(&iter);
	dbus_message_iter_recurse(&iter, &properties);

	call_added(path, vcmanager_path, &properties);

	return TRUE;
}

static void call_removed(const char *path)
{
	struct voice_call *vc;

	DBG("%s", path);

	vc = find_vc(path);
	if (vc == NULL)
		return;

	calls = g_slist_remove(calls, vc);
	call_free(vc);
}

static gboolean handle_vcmanager_call_removed(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	const char *path = NULL;

	audio_wakelock_get();

	if (!dbus_message_get_args(msg, NULL,
				DBUS_TYPE_OBJECT_PATH, &path,
				DBUS_TYPE_INVALID)) {
		error("Unexpected signature in %s.%s signal",
					dbus_message_get_interface(msg),
					dbus_message_get_member(msg));
		return TRUE;
	}

	call_removed(path);

	return TRUE;
}

static gboolean handle_manager_modem_added(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	DBusMessageIter iter, properties;
	const char *path;

	audio_wakelock_get();

	if (modem_obj_path != NULL)
		return TRUE;

	dbus_message_iter_init(msg, &iter);

	if (dbus_message_iter_get_arg_type(&iter)
						!= DBUS_TYPE_OBJECT_PATH) {
		error("Unexpected signature in %s.%s signal",
					dbus_message_get_interface(msg),
					dbus_message_get_member(msg));
		return TRUE;
	}

	dbus_message_iter_get_basic(&iter, &path);
	dbus_message_iter_next(&iter);
	dbus_message_iter_recurse(&iter, &properties);

	modem_added(path, &properties);

	return TRUE;
}

static gboolean handle_manager_modem_removed(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	const char *path;

	audio_wakelock_get();

	if (!dbus_message_get_args(msg, NULL,
				DBUS_TYPE_OBJECT_PATH, &path,
				DBUS_TYPE_INVALID)) {
		error("Unexpected signature in %s.%s signal",
					dbus_message_get_interface(msg),
					dbus_message_get_member(msg));
		return TRUE;
	}

	modem_removed(path);

	return TRUE;
}

static gboolean statefs_batt_update(gint fd, GIOCondition cond, gpointer data)
{
	gchar buf[8];
	gchar *endp = NULL;
	guint64 val;
	int r;

	audio_wakelock_get();

	if ((cond & G_IO_ERR) || (cond & G_IO_NVAL) || (cond & G_IO_HUP)) {
		error("Failed to read battery charge.");
		goto fail;
	}

	DBG("Reading battery charge from fd %d", statefs_batt_fd);
	memset(buf, 0, sizeof(buf));
	r = read(statefs_batt_fd, buf, sizeof(buf) - 1);
	if (r < 0) {
		error("Failed to read battery charge: %s (%d)",
			strerror(errno), errno);
		goto fail;
	} else if (r == 0) {
		error("End of file for fd %d", statefs_batt_fd);
		goto fail;
	}

	lseek(statefs_batt_fd, 0, SEEK_SET);

	DBG("Read charge value: '%s'", buf);
	val = g_ascii_strtoull(buf, &endp, 10);
	if (endp == NULL || *endp != '\0') {
		error("Cannot process battery charge string '%s'", buf);
		goto fail;
	}

	DBG("Battery charge changed to %llu", val);
	val = MIN(5, 5*(val+10)/100);
	telephony_update_indicator(ofono_indicators, "battchg", val);

	return TRUE;

fail:
	close(statefs_batt_fd);
	statefs_batt_fd = -1;
	return FALSE;
}

static void hal_battery_level_reply(DBusPendingCall *call, void *user_data)
{
	DBusMessage *reply;
	DBusError err;
	dbus_int32_t level;
	int *value = user_data;

	reply = dbus_pending_call_steal_reply(call);

	dbus_error_init(&err);
	if (dbus_set_error_from_message(&err, reply)) {
		error("hald replied with an error: %s, %s",
				err.name, err.message);
		dbus_error_free(&err);
		goto done;
	}

	dbus_error_init(&err);
	if (dbus_message_get_args(reply, &err,
				DBUS_TYPE_INT32, &level,
				DBUS_TYPE_INVALID) == FALSE) {
		error("Unable to parse GetPropertyInteger reply: %s, %s",
							err.name, err.message);
		dbus_error_free(&err);
		goto done;
	}

	*value = (int) level;

	if (value == &battchg_last)
		DBG("telephony-ofono: battery.charge_level.last_full"
					" is %d", *value);
	else if (value == &battchg_design)
		DBG("telephony-ofono: battery.charge_level.design"
					" is %d", *value);
	else
		DBG("telephony-ofono: battery.charge_level.current"
					" is %d", *value);

	if ((battchg_design > 0 || battchg_last > 0) && battchg_cur >= 0) {
		int new, max;

		if (battchg_last > 0)
			max = battchg_last;
		else
			max = battchg_design;

		new = battchg_cur * 5 / max;

		telephony_update_indicator(ofono_indicators, "battchg", new);
	}
done:
	dbus_message_unref(reply);
	remove_pending(call);
}

static void hal_get_integer(const char *path, const char *key, void *user_data)
{
	send_method_call("org.freedesktop.Hal", path,
			"org.freedesktop.Hal.Device",
			"GetPropertyInteger",
			hal_battery_level_reply, user_data,
			DBUS_TYPE_STRING, &key,
			DBUS_TYPE_INVALID);
}

static gboolean handle_hal_property_modified(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	const char *path;
	DBusMessageIter iter, array;
	dbus_int32_t num_changes;

	path = dbus_message_get_path(msg);

	dbus_message_iter_init(msg, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_INT32) {
		error("Unexpected signature in hal PropertyModified signal");
		return TRUE;
	}

	dbus_message_iter_get_basic(&iter, &num_changes);
	dbus_message_iter_next(&iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error("Unexpected signature in hal PropertyModified signal");
		return TRUE;
	}

	dbus_message_iter_recurse(&iter, &array);

	while (dbus_message_iter_get_arg_type(&array) != DBUS_TYPE_INVALID) {
		DBusMessageIter prop;
		const char *name;
		dbus_bool_t added, removed;

		dbus_message_iter_recurse(&array, &prop);

		if (!iter_get_basic_args(&prop,
					DBUS_TYPE_STRING, &name,
					DBUS_TYPE_BOOLEAN, &added,
					DBUS_TYPE_BOOLEAN, &removed,
					DBUS_TYPE_INVALID)) {
			error("Invalid hal PropertyModified parameters");
			break;
		}

		if (g_str_equal(name, "battery.charge_level.last_full"))
			hal_get_integer(path, name, &battchg_last);
		else if (g_str_equal(name, "battery.charge_level.current"))
			hal_get_integer(path, name, &battchg_cur);
		else if (g_str_equal(name, "battery.charge_level.design"))
			hal_get_integer(path, name, &battchg_design);

		dbus_message_iter_next(&array);
	}

	return TRUE;
}

static void add_watch(const char *sender, const char *path,
				const char *interface, const char *member,
				GDBusSignalFunction function)
{
	guint watch;

	watch = g_dbus_add_signal_watch(connection, sender, path, interface,
					member, function, NULL, NULL);

	watches = g_slist_prepend(watches, GUINT_TO_POINTER(watch));
}

static void hal_find_device_reply(DBusPendingCall *call, void *user_data)
{
	DBusMessage *reply;
	DBusError err;
	DBusMessageIter iter, sub;
	int type;
	const char *path;

	DBG("begin of hal_find_device_reply()");
	reply = dbus_pending_call_steal_reply(call);

	dbus_error_init(&err);

	if (dbus_set_error_from_message(&err, reply)) {
		error("hald replied with an error: %s, %s",
				err.name, err.message);
		dbus_error_free(&err);
		goto done;
	}

	dbus_message_iter_init(reply, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error("Unexpected signature in hal_find_device_reply()");
		goto done;
	}

	dbus_message_iter_recurse(&iter, &sub);

	type = dbus_message_iter_get_arg_type(&sub);

	if (type != DBUS_TYPE_OBJECT_PATH && type != DBUS_TYPE_STRING) {
		error("No hal device with battery capability found");
		goto done;
	}

	dbus_message_iter_get_basic(&sub, &path);

	DBG("telephony-ofono: found battery device at %s", path);

	add_watch(NULL, path, "org.freedesktop.Hal.Device",
			"PropertyModified", handle_hal_property_modified);

	hal_get_integer(path, "battery.charge_level.last_full", &battchg_last);
	hal_get_integer(path, "battery.charge_level.current", &battchg_cur);
	hal_get_integer(path, "battery.charge_level.design", &battchg_design);
done:
	dbus_message_unref(reply);
	remove_pending(call);
}

static void handle_service_connect(DBusConnection *conn, void *user_data)
{
	DBG("telephony-ofono: %s found", OFONO_BUS_NAME);

	audio_wakelock_get();

	send_method_call(OFONO_BUS_NAME, OFONO_PATH,
				OFONO_MANAGER_INTERFACE, "GetModems",
				get_modems_reply, NULL, DBUS_TYPE_INVALID);
}

static void handle_service_disconnect(DBusConnection *conn, void *user_data)
{
	DBG("telephony-ofono: %s exitted", OFONO_BUS_NAME);

	audio_wakelock_get();

	if (modem_obj_path)
		modem_removed(modem_obj_path);
}

static int statefs_batt_init(const char *path)
{
	statefs_batt_fd = open(path, O_RDONLY | O_DIRECT);
	if (statefs_batt_fd < 0) {
		error("open(%s) failed: %s (%d)", path, strerror(errno), errno);
		return -errno;
	}
	statefs_batt_watch = g_unix_fd_add(statefs_batt_fd,
						G_IO_IN | G_IO_ERR | G_IO_NVAL | G_IO_HUP,
						statefs_batt_update, NULL);

	DBG("Statefs battery info source set up. ");
	return 0;
}

int telephony_init(uint32_t disabled_features, uint32_t disabled_supp_features,
		enum batt_info_source batt, void *batt_param,
		gchar *last_number_path)
{
	const char *battery_cap = "battery";
	const char *chld_str = NULL;
	int ret;
	guint watch;

	telephony_features = AG_FEATURE_EC_ANDOR_NR |
				AG_FEATURE_INBAND_RINGTONE |
				AG_FEATURE_REJECT_A_CALL |
				AG_FEATURE_ENHANCED_CALL_STATUS |
				AG_FEATURE_ENHANCED_CALL_CONTROL |
				AG_FEATURE_EXTENDED_ERROR_RESULT_CODES |
				AG_FEATURE_THREE_WAY_CALLING;
	telephony_features &= ~disabled_features;

	telephony_supp_features = AG_FEATURE_SUPP_CONF_CALL;
	telephony_supp_features &= ~disabled_supp_features;
	
	connection = dbus_bus_get(DBUS_BUS_SYSTEM, NULL);

	add_watch(OFONO_BUS_NAME, NULL, OFONO_MODEM_INTERFACE,
			"PropertyChanged", handle_modem_property_changed);
	add_watch(OFONO_BUS_NAME, NULL, OFONO_NETWORKREG_INTERFACE,
			"PropertyChanged", handle_network_property_changed);
	add_watch(OFONO_BUS_NAME, NULL, OFONO_MANAGER_INTERFACE,
			"ModemAdded", handle_manager_modem_added);
	add_watch(OFONO_BUS_NAME, NULL, OFONO_MANAGER_INTERFACE,
			"ModemRemoved", handle_manager_modem_removed);
	add_watch(OFONO_BUS_NAME, NULL, OFONO_VCMANAGER_INTERFACE,
			"CallAdded", handle_vcmanager_call_added);
	add_watch(OFONO_BUS_NAME, NULL, OFONO_VCMANAGER_INTERFACE,
			"CallRemoved", handle_vcmanager_call_removed);

	watch = g_dbus_add_service_watch(connection, OFONO_BUS_NAME,
						handle_service_connect,
						handle_service_disconnect,
						NULL, NULL);
	if (watch == 0)
		return -ENOMEM;

	watches = g_slist_prepend(watches, GUINT_TO_POINTER(watch));

	switch (batt) {

	case BATT_INFO_STATEFS:
		ret = statefs_batt_init(batt_param);
		break;

	case BATT_INFO_HAL:
	default:
		ret = send_method_call("org.freedesktop.Hal",
				"/org/freedesktop/Hal/Manager",
				"org.freedesktop.Hal.Manager",
				"FindDeviceByCapability",
				hal_find_device_reply, NULL,
				DBUS_TYPE_STRING, &battery_cap,
				DBUS_TYPE_INVALID);
		break;

	}

	if (ret < 0)
		return ret;

	if (last_number_path)
		last_dialed_number_path = g_strdup(last_number_path);

	DBG("telephony_init() successfully");

	if (!(telephony_supp_features & AG_FEATURE_SUPP_CONF_CALL)) {
		chld_str =
			(telephony_features & AG_FEATURE_ENHANCED_CALL_CONTROL)
			? "0,1,1x,2,2x"
			: "0,1,2";
	} else {
		chld_str =
			(telephony_features & AG_FEATURE_ENHANCED_CALL_CONTROL)
			? "0,1,1x,2,2x,3,4"
			: "0,1,2,3,4";
	}

	telephony_ready_ind(telephony_features, ofono_indicators,
					BTRH_NOT_SUPPORTED, chld_str);

	return ret;
}

static void remove_watch(gpointer data)
{
	g_dbus_remove_watch(connection, GPOINTER_TO_UINT(data));
}

static void pending_free(void *data)
{
	DBusPendingCall *call = data;

	if (!dbus_pending_call_get_completed(call))
		dbus_pending_call_cancel(call);

	dbus_pending_call_unref(call);
}

void telephony_exit(void)
{
	DBG("");

	g_free(last_dialed_number);
	last_dialed_number = NULL;

	g_free(last_dialed_number_path);
	last_dialed_number_path = NULL;

	if (modem_obj_path)
		modem_removed(modem_obj_path);

	g_slist_free_full(watches, remove_watch);
	watches = NULL;

	g_slist_free_full(pending, pending_free);
	pending = NULL;

	dbus_connection_unref(connection);
	connection = NULL;

	if (statefs_batt_watch != 0) {
		g_source_remove(statefs_batt_watch);
		statefs_batt_watch = 0;
	}

	if (statefs_batt_fd >= 0) {
		close(statefs_batt_fd);
		statefs_batt_fd = -1;
	}

	telephony_deinit();
}
