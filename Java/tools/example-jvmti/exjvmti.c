
#include <stdio.h>
#include <string.h>
#include "jni.h"
#include "jvmti.h"

static void
check_jvmti_errors (jvmtiEnv *jvmti, jvmtiError errnum, const char *str)
{

  if (errnum != JVMTI_ERROR_NONE)
    {

      char *errnum_str;
      errnum_str = NULL;
      (void) (*jvmti)->GetErrorName (jvmti, errnum, &errnum_str);
      printf ("ERROR: JVMTI: [%d] %s - %s", errnum,
	      (errnum_str == NULL ? "Unknown" : errnum_str),
	      (str == NULL ? "" : str));
    }

}

static void JNICALL callbackMethodEntry (jvmtiEnv *jvmti, JNIEnv *jni, jthread thread, jmethodID method)
  {

    char *name_ptr;
    char *signature_ptr;
    char *generic_ptr;
    jvmtiError error;
    error = (*jvmti)->GetMethodName (jvmti, method, &name_ptr, &signature_ptr,
	&generic_ptr);
    check_jvmti_errors (jvmti, error, "Unable to get the method name");
    printf ("Entered method %s\n", name_ptr);
  }

JNIEXPORT jint JNICALL
Agent_OnLoad (JavaVM *jvm, char *options, void *reserved)
{

  jvmtiEnv *jvmti;
  jvmtiError error;
  jint res;
  jvmtiEventCallbacks callbacks;
  jvmtiCapabilities capa;
  jrawMonitorID rawMonitorID;
  // Get the JVMTI environment

  res = (*jvm)->GetEnv (jvm, (void**) &jvmti, JVMTI_VERSION_1_0);
  if (res != JNI_OK || jvmti == NULL)
    {

      printf ("Unable to get access to JVMTI version 1.0");
    }

  (void) memset(&capa, 0, sizeof(jvmtiCapabilities));
  // Let's initialize the capabilities

  capa.can_generate_method_entry_events = 1;
  error = (*jvmti)->AddCapabilities (jvmti, &capa);
  check_jvmti_errors (jvmti, error, "Unable to add the required capabilities");
  // Setup event notification

  error = (*jvmti)->SetEventNotificationMode (jvmti, JVMTI_ENABLE,
					      JVMTI_EVENT_METHOD_ENTRY,
					      (jthread) NULL);
  check_jvmti_errors (jvmti, error,
		      "Unable to set the event notification mode");
  // Setup the callbacks

  (void) memset(&callbacks, 0, sizeof(callbacks));

  callbacks.MethodEntry = &callbackMethodEntry;
  error = (*jvmti)->SetEventCallbacks (jvmti, &callbacks,
				       (jint) sizeof(callbacks));
  check_jvmti_errors (jvmti, error, "Unable to set event callbacks");
  // Get the raw monitor

  error = (*jvmti)->CreateRawMonitor (jvmti, "JVMTI agent data", &rawMonitorID);
  check_jvmti_errors (jvmti, error, "Unable to create a Raw monitor");
  return JNI_OK;
}