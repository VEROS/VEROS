#ifndef MVBONCE_BA_H
#define MVBONCE_BA_H
//=============================================================================
//
//      ba.h
//
//      Bus administrator header
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Yinlong Su
// Date:        2012-08-16
// Modified:	2012-11-09
// Description: Bus administrator header
// Version:     1.0
// Usage:       #include "ba.h"
//
//####DESCRIPTIONEND####
//
//=============================================================================
#include "mvb_project.h"
#include "mvb_def.h"
#include "hal.h"
#include <cyg/kernel/kapi.h>
#include <stdlib.h>
#include <stdio.h>

#ifndef MVBPROJ_DEFAULT_BA_MAX_BASIC_PERIOD
	#define BA_MAX_BASIC_PERIOD 1024
#else
	#define BA_MAX_BASIC_PERIOD MVBPROJ_DEFAULT_BA_MAX_BASIC_PERIOD
#endif

#define BA_ADMIN_BAL_SIZE 		(64 + 1)

#define BA_CONTEXT_NOTRUNNING			0
#define BA_CONTEXT_DEVICES_SCAN			1
#define BA_CONTEXT_MASTERSHIP_TRANSFER	2
#define BA_CONTEXT_MESSAGE_ARBITRATION	3

#define BA_CONTEXT_MASTERSHIP_TRANSFER_NULL				0
#define BA_CONTEXT_MASTERSHIP_TRANSFER_DEVICE_STATUS	1
#define BA_CONTEXT_MASTERSHIP_TRANSFER_OFFER_MASTERSHIP	2

#define MVB_MASTERSHIP_TRANSFER_RESPONSE_BIT_ACP 0x8000

#define RS_CODE_MASTERSHIP_TRANSFER_STATES_OK			0
#define RS_CODE_MASTERSHIP_TRANSFER_STATES_ERROR		1
#define RS_CODE_MASTERSHIP_TRANSFER_KEEP				2
#define RS_CODE_MASTERSHIP_TRANSFER_INTERIM_TIMEOUT		3
#define RS_CODE_MASTERSHIP_TRANSFER_REMOTE_REJECT		4
#define RS_CODE_MASTERSHIP_TRANSFER_WORK				5

#define RS_CODE_DEVICES_SCAN_OK							0
#define RS_CODE_DEVICES_SCAN_FIN						1

#define RS_CODE_OK	0

#define MVB_SIZEOF_STRUCT_MVB_ADMINISTRATOR_KDL 2
typedef struct
{
	BITFIELD16  device_address;
} MVB_ADMINISTRATOR_KDL;

/* --------------------------------------------------------------------------
 *  Macro     : SV_MVB_ADMINISTRATOR_GET_C_KDL
 *
 *  Purpose   : Returns the number of entries of the 'known devices list'.
 *
 *  Input     : _p_base_ - pointer to base of MVB_Administrator object
 *
 *  Return    : number of entires of the 'known devices list'
 * --------------------------------------------------------------------------
 */
#define MVB_ADMINISTRATOR_GET_C_KDL(_p_base_)                            \
        (UNSIGNED16)                                                        \
        (                                                                   \
            (                                                               \
                (_p_base_)->reserved_list_offset -                          \
                (_p_base_)->known_devices_list_offset                       \
            ) / 2                                                           \
        )


/* --------------------------------------------------------------------------
 *  Macro     : SV_MVB_ADMINISTRATOR_GET_P_KDL
 *
 *  Purpose   : Returns the pointer to first entry
 *              of the 'known devices list' or NULL if list is empty.
 *
 *  Input     : _p_base_ - pointer to base of MVB_Administrator object
 *
 *  Return    : pointer to first entry of the 'known devices list'
 *              or NULL if list is empty
 * --------------------------------------------------------------------------
 */
#define MVB_ADMINISTRATOR_GET_P_KDL(_p_base_)                            \
        (                                                                   \
            ((_p_base_)->known_devices_list_offset ==                       \
             (_p_base_)->reserved_list_offset)                              \
            ? (MVB_ADMINISTRATOR_KDL*)NULL                                  \
            : (MVB_ADMINISTRATOR_KDL*)                                      \
              (                                                             \
                  (_p_base_)->known_devices_list                            \
              )                                                             \
        )


void ba_structure();
void ba_init(bool flag_send);
void ba_context_process(UNSIGNED8 sf_f_code, UNSIGNED16 sf_content_16, UNSIGNED8 vector);
void md_context_process(UNSIGNED8 vector);
UNSIGNED8 mastership_transfer(UNSIGNED8 sf_f_code, UNSIGNED16 sf_content_16, UNSIGNED8 vector);
UNSIGNED8 devices_scan(UNSIGNED8 sf_f_code, UNSIGNED16 sf_content_16, UNSIGNED8 vector);
UNSIGNED8 build_list_of_devices_scan(UNSIGNED16 address, BITSET16 status, bool flag_remove);
void supervisory_interrupt_handle();

#endif // ifndef MVBONCE_BA_H
