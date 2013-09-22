//=============================================================================
//
//      ba.c
//
//      Bus administrator C file
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Yinlong Su
// Date:        2012-06-06
// Modified:	2012-11-09
// Description: Bus administrator C file
// Version:     2.0
//
//####DESCRIPTIONEND####
//
//=============================================================================

#include "ba.h"

//=============================================================================
// Variable Description
//
// int bp_number :: Number of current basic period.
//
// UNSIGNED16 ba_mf :: Last main frame of this master device.
//                     (For conflict detection)
//
// UNSIGNED8 ba_context	:: Current BA context action.
//                      01. BA_CONTEXT_NOTRUNNING : not current master, exit;
//                      02. BA_CONTEXT_DEVICES_SCAN : devices scan;
//                      03. BA_CONTEXT_MASTERSHIP_TRANSFER : mastership transfer;
//                      04. BA_CONTEXT_MESSAGE_ARBITRATION : message arbitration.
//
// UNSIGNED8  device_scan_unit :: Number of devices need to be scaned of current
//                                basic period.
// UNSIGNED8  ba_context_devices_scan_i :: Array index of current scan device
//                                         in KDL.
// UNSIGNED8  ba_context_devices_scan_j :: Number of scaned devices of current
//                                         basic period.
// UNSIGNED16 ba_context_devices_scan_address :: Address of current device.
//                                               (devices scan)
//
// UNSIGNED16 ba_context_mastership_transfer_address :: Address of current device
//                                                      (mastership transfer)
// UNSIGNED8  ba_context_mastership_transfer_act :: Current MT context action.
//                         01. BA_CONTEXT_MASTERSHIP_TRANSFER_NULL
//                         02. BA_CONTEXT_MASTERSHIP_TRANSFER_DEVICE_STATUS
//                         03. BA_CONTEXT_MASTERSHIP_TRANSFER_OFFER_MASTERSHIP
//
// MVB_ADMINISTRATOR* admin_obj :: Pointer to MVB_ADMINISTRATOR object
// ENUM16 devices_scan_strategy :: Strategy of devices scan in MVB_ADMINISTRATOR.
//
// cyg_uint16 devices_list[] :: Device status table
//                              (address less than BA_ADMIN_BAL_SIZE) 
// cyg_uint16 devices_list_timeout_count[] :: Device scan timeout count table
//                                            (address less than BA_ADMIN_BAL_SIZE)
//
// cyg_resolution_t standup_clock_resolution :: Clock resolution for backup BA.
// cyg_tick_count_t standup_clock_count      :: Clock count for backup BA.
int bp_number = 0;

UNSIGNED8  ba_context = BA_CONTEXT_NOTRUNNING;

UNSIGNED16 ba_mf;

UNSIGNED8  device_scan_unit;
UNSIGNED8  ba_context_devices_scan_i;
UNSIGNED8  ba_context_devices_scan_j;
UNSIGNED16 ba_context_devices_scan_address;

UNSIGNED16 ba_context_mastership_transfer_address;
UNSIGNED8  ba_context_mastership_transfer_act;

MVB_ADMINISTRATOR *admin_obj;
ENUM16 devices_scan_strategy;

cyg_uint16 devices_list[BA_ADMIN_BAL_SIZE];
cyg_uint16 devices_list_timeout_count[BA_ADMIN_BAL_SIZE];


//*********************************************
//add by lqc for messagedata optimize
//*********************************************
#define md_get_pre(address)  ( ( md_ability_array[address].pre_high << 8 )  + md_ability_array[address].pre_low )
#define md_get_next(address) ( ( md_ability_array[address].next_high << 8 ) + md_ability_array[address].next_low )
#define md_set_pre( address , value ) 	{\
											md_ability_array[address].pre_high = ( value >> 8 );\
											md_ability_array[address].pre_low = ( value & 0xff);\
										}
#define md_set_next( address , value )	{\
											md_ability_array[address].next_high = ( value >> 8 );\
											md_ability_array[address].next_low = ( value & 0xff);\
										}
struct MD_ABILITY_NODE
{
	UNSIGNED8 pre_high:4;
	UNSIGNED8 next_high:4;
	UNSIGNED8 pre_low:8;
	UNSIGNED8 next_low:8;
	
};
extern struct MD_ABILITY_NODE md_ability_array[4096];
extern UNSIGNED8 md_ability_count;



extern UNSIGNED16 this_addr;
extern MVB_ADMINISTRATOR mvb_administrator;
extern MVB_DEVICE_STATUS mvb_device_status;
extern cyg_uint16 mvb_device_status_16;
extern UNSIGNED16 current_mf;

#ifdef MVBPROJ_DEBUG_REALTIME
int mp_number = 0;
extern int _debug_success_mf, _debug_success_sf;
extern int _debug_fail_mf, _debug_fail_sf;
extern int _debug_err_mf, _debug_err_sf;
extern int _debug_sync;
#endif

#ifdef MVBPROJ_DEBUG_CONN_BA
int _conn_ba_flag = -1;
#endif

/* --------------------------------------------------------------------------
 *  ba_structure
 *
 *  Bus administrator structure creation
 *
 *  @param	: void
 *  @return	: void
 *
 *  Initialization:
 *    01. devices_list[BA_ADMIN_BAL_SIZE];
 *    02. devices_list_timeout_count[BA_ADMIN_BAL_SIZE].
 * --------------------------------------------------------------------------
 */
void ba_structure()
{
	int i;
	for (i = 0; i < BA_ADMIN_BAL_SIZE; i++)
	{
		devices_list[i] = 0;
		devices_list_timeout_count[i] = 0;
	}
	

}

/* --------------------------------------------------------------------------
 *  ba_init
 *
 *  Bus administrator Initialization
 *
 *  @param		: bool flag_send
 *  @return		: void
 *  @condition	: current master
 *
 *  Process:
 *    01. Master LED on;
 *    02. Initialize context for devices scan (according to scan strategy);
 *    03. Send status to FPGA.
 * --------------------------------------------------------------------------
 */
void ba_init(bool flag_send)
{
#ifdef MVBPROJ_LED_SUPPORT
	mvb_arm_master_led(1);
#endif

#ifdef MVBPROJ_DEBUG_INFO
	printf("[BA] Init called.\n");
#endif

#ifdef MVBPROJ_DEBUG_REALTIME
	_debug_success_mf = 0, _debug_success_sf = 0;
	_debug_fail_mf = 0, _debug_fail_sf = 0;
#endif

	mvb_device_status.cs3 = 1; // MAS
	mvb_device_status_16 = *((cyg_uint16*)&mvb_device_status);
	
	bp_number = 0;
	ba_context = BA_CONTEXT_NOTRUNNING;

	ba_context_devices_scan_i = 0;

	admin_obj = &mvb_administrator;
	devices_scan_strategy = admin_obj->devices_scan_strategy;

	if (devices_scan_strategy == DEVICES_SCAN_STRATEGY_ENUM_KNOWN)
	{
#ifdef MVBPROJ_DEBUG_INFO
	printf("[BA] Devices scan strategy: KNOWN.\n");
#endif
		UNSIGNED32 KDL_BASE = (UNSIGNED32) MVB_ADMINISTRATOR_GET_P_KDL(admin_obj);
		UNSIGNED16 count = MVB_ADMINISTRATOR_GET_C_KDL(admin_obj);
		UNSIGNED16 address;
		do
		{
			if (ba_context_devices_scan_i >= count)
			{
				ba_context_devices_scan_i = 0;
				break;
			}

			UNSIGNED32	KDL_CURRENT_ENTRY = KDL_BASE + ba_context_devices_scan_i * MVB_SIZEOF_STRUCT_MVB_ADMINISTRATOR_KDL;
			MVB_ADMINISTRATOR_KDL *entry = (MVB_ADMINISTRATOR_KDL *)KDL_CURRENT_ENTRY;
			address = entry->device_address;
			ba_context_devices_scan_i++;
		}while (address != ba_context_devices_scan_address);
		if (ba_context_devices_scan_i > 0)
			ba_context_devices_scan_i --;


	}
	else
	{
#ifdef MVBPROJ_DEBUG_INFO
	printf("[BA] Devices scan strategy: ALL.\n");
#endif
	}
	
	if (flag_send == true)
	{
#ifdef MVBPROJ_DEBUG_INFO
		printf("SED SYNC.\n");
#endif

		mvb_arm_send_status(mvb_device_status_16);
	}
}

/* --------------------------------------------------------------------------
 *  ba_context_process
 *
 *  Bus administrator interrupts context process
 *
 *  @param		: UNSIGNED8		sf_f_code
 *                UNSIGNED16	sf_content_16
 *                UNSIGNED8		vector
 *  @return		: void
 *  @condition	: current master
 *  @see		: devices_scan, mastership_transfer, md_context_process
 *
 *  When current master receive multiple different interrupts, this function
 *  help to distribute interrupt vector and frame data to handle function
 *  according to bus administrator context.
 *
 *  ba_context (current ba context):
 *    01. BA_CONTEXT_NOTRUNNING				: not current master, exit;
 *    02. BA_CONTEXT_DEVICES_SCAN			: devices scan;
 *    03. BA_CONTEXT_MASTERSHIP_TRANSFER	: mastership transfer;
 *    04. BA_CONTEXT_MESSAGE_ARBITRATION	: message arbitration.
 * --------------------------------------------------------------------------
 */
void ba_context_process(UNSIGNED8 sf_f_code, UNSIGNED16 sf_content_16, UNSIGNED8 vector)
{
#ifdef MVBPROJ_DEBUG_INFO
	printf("[BA] Context process called.\n");
#endif
	if (ba_context == BA_CONTEXT_NOTRUNNING)
		return;

	UNSIGNED8 rs_code;
	switch (ba_context)
	{
	case BA_CONTEXT_DEVICES_SCAN:
		rs_code = RS_CODE_DEVICES_SCAN_FIN;
#ifndef MVBPROJ_DEVICES_SCAN_BLOCKED
		rs_code = devices_scan(sf_f_code, sf_content_16, vector);
#endif // ifndef MVBPROJ_DEVICES_SCAN_BLOCKED
		if (rs_code == RS_CODE_DEVICES_SCAN_FIN)
		{
			ba_context = BA_CONTEXT_MESSAGE_ARBITRATION;
#ifndef MVBPROJ_ARBITRATION_BLOCKED
		md_context_process(EXTI_SUPERVISORY_INT_VECTOR);
#endif // ifndef MVBPROJ_MASTERSHIP_TRANSFER_BLOCKED	
		}
		break;
	case BA_CONTEXT_MASTERSHIP_TRANSFER:
#ifndef MVBPROJ_MASTERSHIP_TRANSFER_BLOCKED
#ifdef MVBPROJ_DEBUG_CONN_BA
cyg_interrupt_disable();
printf("bp_number: %d\n", bp_number);
cyg_interrupt_enable();
#endif
		rs_code = mastership_transfer(sf_f_code, sf_content_16, vector);
#endif // ifndef MVBPROJ_MASTERSHIP_TRANSFER_BLOCKED
		break;
	case BA_CONTEXT_MESSAGE_ARBITRATION:
#ifndef MVBPROJ_ARBITRATION_BLOCKED
		md_context_process(vector);
#endif // ifndef MVBPROJ_MASTERSHIP_TRANSFER_BLOCKED	
		break;
	}
}

/* --------------------------------------------------------------------------
 *  md_context_process
 *
 *  Message phase context process
 *
 *  @param		: UNSIGNED8		sf_f_code
 *                UNSIGNED16	sf_content_16
 *                UNSIGNED8		vector
 *  @return		: void
 *  @condition	: current master
 *  @see		: bsp_handler, slaveframe_handler, timeout_handler, collision_handler
 *
 *  When current master process message data and receive multiple different
 *  interrupts, this function help to distribute interrupt vector and frame
 *  data to handle function
 * --------------------------------------------------------------------------
 */
void md_context_process(UNSIGNED8 vector)
{
	if (vector == EXTI_SUPERVISORY_INT_VECTOR)
		bsp_handler();
	else if (vector == EXTI_SLAVE_FRAME_VECTOR)
		slaveframe_handler();
	else if (vector == EXTI_TIMEOUT_VECTOR)
		timeout_handler();
	else if  (vector == EXTI_ERROR_FRAME_VECTOR)
		collision_handler();
}

/* --------------------------------------------------------------------------
 *  mastership_transfer
 *
 *  Mastrship transfer function
 *
 *  @param		: UNSIGNED8		sf_f_code
 *                UNSIGNED16	sf_content_16
 *                UNSIGNED8		vector
 *  @return		: UNSIGNED8		rs_code
 *  @condition	: current master
 *
 *  At the end of macro cycle, current master shall try to pass mastership to
 *  other backup administrator, or keep mastership when no other
 *  administrator available. This function should be called only once at each
 *  macro cycle.
 *
 *  ba_context_mastership_transfer_act (current action context):
 *    01. BA_CONTEXT_MASTERSHIP_TRANSFER_NULL :
 *          First action, ready to send device scan frame to scan device
 *        address ba_context_mastership_transfer_address.
 *    02. BA_CONTEXT_MASTERSHIP_TRANSFER_DEVICE_STATUS :
 *          Wait for device status slave frame. If status.ba == 1 &&
 *        status.cs2 == 1, offer mastership and change context to
 *        BA_CONTEXT_MASTERSHIP_TRANSFER_OFFER_MASTERSHIP. If not, return to
 *        context BA_CONTEXT_MASTERSHIP_TRANSFER_NULL to send another device
 *        scan main frame.
 *    03. BA_CONTEXT_MASTERSHIP_TRANSFER_OFFER_MASTERSHIP
 *          Wait for backup administrator to response F_Code = 8 main frame.
 *        Slave frame with the most significant bit as 1 means transfer
 *        succeed. Others will lead to keep mastership for current master.
 * --------------------------------------------------------------------------
 */
UNSIGNED8 mastership_transfer(UNSIGNED8 sf_f_code, UNSIGNED16 sf_content_16, UNSIGNED8 vector)
{

	if (vector == EXTI_SUPERVISORY_INT_VECTOR)
	{
#ifdef MVBPROJ_DEBUG_CONN_BA
	diag_printf("\t[MASTERSHIP TRANSFER] VECTOR: SUPERVISORY_INT\n");
#endif

		ba_context_mastership_transfer_address = (this_addr + 1) % BA_ADMIN_BAL_SIZE;
		while (ba_context_mastership_transfer_address != this_addr)
		{
			if (((devices_list[ba_context_mastership_transfer_address] >> 14) % 2) == 1)
			{
				break;
			}
			ba_context_mastership_transfer_address ++;
			ba_context_mastership_transfer_address = ba_context_mastership_transfer_address % BA_ADMIN_BAL_SIZE;
		}
		
		ba_context_mastership_transfer_act = BA_CONTEXT_MASTERSHIP_TRANSFER_NULL;
#ifdef MVBPROJ_DEBUG_CONN_BA
	cyg_interrupt_disable();
	printf("\t[MASTERSHIP TRANSFER] address = %d\n", ba_context_mastership_transfer_address);
	cyg_interrupt_enable();
#endif
		if (ba_context_mastership_transfer_address == this_addr)
		{
			return RS_CODE_MASTERSHIP_TRANSFER_KEEP;
		}
	}

	if (vector == EXTI_TIMEOUT_VECTOR)
	{
		if (ba_context_mastership_transfer_act == BA_CONTEXT_MASTERSHIP_TRANSFER_DEVICE_STATUS ||
			ba_context_mastership_transfer_act == BA_CONTEXT_MASTERSHIP_TRANSFER_OFFER_MASTERSHIP)
		{
			ba_context_mastership_transfer_address = (ba_context_mastership_transfer_address + 1) % BA_ADMIN_BAL_SIZE;
			while (ba_context_mastership_transfer_address != this_addr)
			{
				if (((devices_list[ba_context_mastership_transfer_address] >> 14) % 2) == 1)
				{
					break;
				}
				ba_context_mastership_transfer_address ++;
				ba_context_mastership_transfer_address = ba_context_mastership_transfer_address % BA_ADMIN_BAL_SIZE;
			}
			if (ba_context_mastership_transfer_address == this_addr)
			{
				return RS_CODE_MASTERSHIP_TRANSFER_KEEP;
			}
			ba_context_mastership_transfer_act = BA_CONTEXT_MASTERSHIP_TRANSFER_NULL;
		}
	}

#ifdef MVBPROJ_DEBUG_CONN_BA
	cyg_interrupt_disable();
	printf("\t[MASTERSHIP TRANSFER] now address = 0x%04x\n", ba_context_mastership_transfer_address);
	cyg_interrupt_enable();
#endif

	if (vector == EXTI_SLAVE_FRAME_VECTOR)
	{
#ifdef MVBPROJ_DEBUG_CONN_BA
	cyg_interrupt_disable();
	printf("\t[MASTERSHIP TRANSFER] VECTOR: SLAVE_FRAME, sf_f_code=%d, sf_content=0x%04x\n", sf_f_code, sf_content_16);
	cyg_interrupt_enable();
#endif
		if (ba_context_mastership_transfer_act == BA_CONTEXT_MASTERSHIP_TRANSFER_DEVICE_STATUS)
		{
			MVB_DEVICE_STATUS _status = *((MVB_DEVICE_STATUS*)&sf_content_16);
			if (sf_f_code == FRAME_F_CODE_15 && (_status.ba == 1) && (_status.cs2 == 1))
			{
#ifdef MVBPROJ_DEBUG_CONN_BA
	cyg_interrupt_disable();
	printf("\t[MASTERSHIP TRANSFER] mastership offer, address = 0x%04x\n", ba_context_mastership_transfer_address);
	cyg_interrupt_enable();
			_conn_ba_flag = bp_number;
#endif
				ba_context_mastership_transfer_act = BA_CONTEXT_MASTERSHIP_TRANSFER_OFFER_MASTERSHIP;

				mvb_arm_send_main_frame_f(FRAME_F_CODE_8, ba_context_mastership_transfer_address);

			}
			else
			{
				ba_context_mastership_transfer_address = (ba_context_mastership_transfer_address + 1) % BA_ADMIN_BAL_SIZE;
				while (ba_context_mastership_transfer_address != this_addr)
				{
					if (((devices_list[ba_context_mastership_transfer_address] >> 14) % 2) == 1)
					{
						break;
					}
					ba_context_mastership_transfer_address ++;
					ba_context_mastership_transfer_address = ba_context_mastership_transfer_address % BA_ADMIN_BAL_SIZE;
				}
				if (ba_context_mastership_transfer_address == this_addr)
				{
					return RS_CODE_MASTERSHIP_TRANSFER_KEEP;
				}
#ifdef MVBPROJ_DEBUG_CONN_BA
	cyg_interrupt_disable();
	printf("\t[MASTERSHIP TRANSFER] now address = 0x%04x\n", ba_context_mastership_transfer_address);
	cyg_interrupt_enable();
#endif
				ba_context_mastership_transfer_act = BA_CONTEXT_MASTERSHIP_TRANSFER_NULL;
			}
		}
		else if (ba_context_mastership_transfer_act == BA_CONTEXT_MASTERSHIP_TRANSFER_OFFER_MASTERSHIP)
		{
			if (sf_f_code == FRAME_F_CODE_8)
			{
				ba_context = BA_CONTEXT_NOTRUNNING;
				mvb_device_status.cs3 = 0;
				mvb_device_status_16 = *((cyg_uint16*)&mvb_device_status);

#ifdef MVBPROJ_DEBUG_CONN_BA
	cyg_interrupt_disable();
	printf("\t[MASTERSHIP TRANSFER] transfer ok, master address = 0x%04x\n", ba_context_mastership_transfer_address);
	diag_printf("SED SYNC.\n");
	cyg_interrupt_enable();
#endif

#ifdef MVBPROJ_LED_SUPPORT
	mvb_arm_master_led(0);
#endif

				mvb_arm_send_status(mvb_device_status_16);
				return RS_CODE_MASTERSHIP_TRANSFER_STATES_OK;
			}
			else
			{
#ifdef MVBPROJ_DEBUG_CONN_BA
	diag_printf("\t[MASTERSHIP TRANSFER] transfer failed.\n");
#endif


				return RS_CODE_MASTERSHIP_TRANSFER_KEEP;
			}
		}

	}
	if (ba_context_mastership_transfer_act == BA_CONTEXT_MASTERSHIP_TRANSFER_NULL)
	{
#ifdef MVBPROJ_DEBUG_CONN_BA
	cyg_interrupt_disable();
	printf("\t[MASTERSHIP TRANSFER] master status scan, address = 0x%04x\n", ba_context_mastership_transfer_address);
	cyg_interrupt_enable();
#endif

		ba_context_mastership_transfer_act = BA_CONTEXT_MASTERSHIP_TRANSFER_DEVICE_STATUS;
		mvb_arm_send_main_frame_f(FRAME_F_CODE_15, ba_context_mastership_transfer_address);

	}
	return RS_CODE_MASTERSHIP_TRANSFER_WORK;
}

/* --------------------------------------------------------------------------
 *  devices_scan
 *
 *  Devices scan function
 *
 *  @param		: UNSIGNED8		sf_f_code
 *                UNSIGNED16	sf_content_16
 *                UNSIGNED8		vector
 *  @return		: UNSIGNED8		rs_code
 *  @condition	: current master
 *  @see		: build_list_of_devices_scan
 *
 *  Each basic period (except last one in macro cycle), this function send
 *  several device scan frame (F_code = 15) according to the config in binary
 *  file (may be 0 or 1). In the administrator data structure
 *  MVB_ADMINISTRATOR, there is two strategy of devices scan, for all address
 *  and known devices (Also, there's known devices list in MVB_ADMINISTRATOR).
 *  To supervisory the bus, master should poll the status of each device, and
 *  build devices_list to store device status. Device not response for three
 *  times will be deleted from devices_list.
 * --------------------------------------------------------------------------
 */
UNSIGNED8 devices_scan(UNSIGNED8 sf_f_code, UNSIGNED16 sf_content_16, UNSIGNED8 vector)
{
	if (device_scan_unit == 0)
		return RS_CODE_DEVICES_SCAN_FIN;

	if (vector == EXTI_SUPERVISORY_INT_VECTOR)
	{
		ba_context_devices_scan_j = 0;
	}


	if (vector == EXTI_TIMEOUT_VECTOR)
	{
		build_list_of_devices_scan(FRAME_ADDRESS(current_mf), 0, true);
		ba_context_devices_scan_j ++;

	}
	else if (vector == EXTI_SLAVE_FRAME_VECTOR)
	{
		build_list_of_devices_scan(FRAME_ADDRESS(current_mf), sf_content_16, false);
		ba_context_devices_scan_j ++;
	}

    if (ba_context_devices_scan_j >= device_scan_unit)
        return RS_CODE_DEVICES_SCAN_FIN;

	UNSIGNED32	KDL_BASE, KDL_CURRENT_ENTRY;
	UNSIGNED32	count, *entry;
	switch (devices_scan_strategy)
	{
	case DEVICES_SCAN_STRATEGY_ENUM_KNOWN:
		KDL_BASE = (UNSIGNED32) MVB_ADMINISTRATOR_GET_P_KDL(admin_obj);
		count = MVB_ADMINISTRATOR_GET_C_KDL(admin_obj);

		if (ba_context_devices_scan_i >= count)
			ba_context_devices_scan_i = 0;

		KDL_CURRENT_ENTRY	= KDL_BASE + ba_context_devices_scan_i * MVB_SIZEOF_STRUCT_MVB_ADMINISTRATOR_KDL;
		entry				= (UNSIGNED32 *)KDL_CURRENT_ENTRY;

		ba_context_devices_scan_address = *entry;

#ifdef MVBPROJ_DEBUG_INFO
	printf("\t[DEVICES SCAN] F=15 Address=0x%04x (KNOWN)\n", ba_context_devices_scan_address);
#endif
		mvb_arm_send_main_frame_f(FRAME_F_CODE_15, ba_context_devices_scan_address);
		ba_context_devices_scan_i ++;
		break;
	case DEVICES_SCAN_STRATEGY_ENUM_ALL:
		if (ba_context_devices_scan_address >= 0x1000 || ba_context_devices_scan_address <= 0x0000)
			ba_context_devices_scan_address = 0x0001;

#ifdef MVBPROJ_DEBUG_INFO
	printf("\t[DEVICES SCAN] F=15 Address=0x%04x (ALL)\n", ba_context_devices_scan_address);
#endif

		mvb_arm_send_main_frame_f(FRAME_F_CODE_15, ba_context_devices_scan_address);
		ba_context_devices_scan_address ++;
		break;
	}

	return RS_CODE_DEVICES_SCAN_OK;
}

/* --------------------------------------------------------------------------
 *  build_list_of_devices_scan
 *
 *  devices_list build function
 *
 *  @param		: UNSIGNED16	address
 *                BITSET16		status
 *                bool			flag_remove
 *  @return		: UNSIGNED8		rs_code
 *  @condition	: administrator
 *
 *  When receive slave frame responsed to device scan main frame (F_Code = 
 *  15), all administrator should store device status (address less than
 *  BA_ADMIN_BAL_SIZE) to devices_list. Device not response for three
 *  times will be deleted from devices_list.
 * --------------------------------------------------------------------------
 */
UNSIGNED8 build_list_of_devices_scan(
		UNSIGNED16	address,
		BITSET16	status,
		bool		flag_remove)
{
#ifdef MVBPROJ_BUILD_DEVICES_LIST_BLOCKED
	return RS_CODE_OK;
#endif

	//*************************************
	//add by lqc for messagedata optimize
	//*************************************
	if( !flag_remove )
	{
		//发现设备，且设备有消息能力
		if( MVB_DEVICE_STATUS_BIT_MD == ( status & MVB_DEVICE_STATUS_BIT_MD ) )
		{
			if( ( md_ability_count > 1 && md_get_pre(address) == 0 && md_get_next(address) == 0 ) || md_get_next(0) != address )
			{
				//printf( "add %x\n", address );
				md_set_next( address , md_get_next(0) );
				md_set_pre( md_get_next(0) , address );
				md_set_pre( address , 0 );
				md_set_next( 0 , address );
				md_ability_count++;
			}
		}
		//发现设备，且设备没有消息能力
		else
		{
			//以前该设备有消息能力
			if( ( md_ability_count > 1 && ( md_get_pre(address) != 0 || md_get_next(address) != 0 ) ) || md_get_next(0) == address )
			{
				//printf( "remove:%x\n" , address );
				md_set_next( md_get_pre(address) , md_get_next(address));
				md_set_pre( md_get_next(address) , md_get_pre(address));
				md_set_next( address , 0 );
				md_set_pre( address , 0 );
				md_ability_count--;
			}
		}
	}
	//没有该设备
	else
	{
		if( ( md_ability_count > 1 && ( md_get_pre(address) != 0 || md_get_next(address) != 0 ) ) || md_get_next(0) == address )
		{
			//printf( "remove!:%x\n" , address );
			md_set_next( md_get_pre(address) , md_get_next(address));
			md_set_pre( md_get_next(address) , md_get_pre(address));
			md_set_next( address , 0 );
			md_set_pre( address , 0 );
			md_ability_count--;
		}
	}


	/*add by lqc 
	// ba_context_devices_scan_address = address;
	// current master will cause problem, close to disable memory function

	if (address >= BA_ADMIN_BAL_SIZE)
		return RS_CODE_OK;

	if (!flag_remove)
	{
		devices_list_timeout_count[address] = 0;
		devices_list[address] = status;
#ifdef MVBPROJ_DEBUG_CONN_BA
	cyg_interrupt_disable();
	printf("build address: %03x status: %04x\n", address, status);
	cyg_interrupt_enable();
#endif
	}
	else
	{
		devices_list_timeout_count[address]++;
		if (devices_list_timeout_count[address] >= 3)
		{
			devices_list_timeout_count[address] = 0;
			devices_list[address] = 0;
		}
	}
	add by lqc*/
	
	return RS_CODE_OK;
}

/* --------------------------------------------------------------------------
 *  supervisory_interrupt_handle
 *
 *  Supervisory interrupt process handle
 *
 *  @param		: void
 *  @return		: void
 *  @trigger	: supervisory interrupt ISR called
 *  @see		: ba_context_process
 *
 *  Supervisory interrupt process handle
 *
 * --------------------------------------------------------------------------
 */
void supervisory_interrupt_handle()
{
	bp_number++;
	
#ifdef MVBPROJ_DEBUG_INFO
	printf("[HANDLE] SVPROCESS, bp_number = %d\n", bp_number);
#endif

	if (bp_number == BA_MAX_BASIC_PERIOD)
	{

#ifdef MVBPROJ_DEBUG_REALTIME
	mp_number ++;
	cyg_interrupt_disable();
	printf("{%d} VALID: [MF]%d [SF]%d TIMEOUT: [MF]%d [SF]%d ERROR: [MF]%d [SF]%d SYNC %d\n", mp_number, _debug_success_mf, _debug_success_sf, _debug_fail_mf, _debug_fail_sf, _debug_err_mf, _debug_err_sf, _debug_sync);
	_debug_success_mf = 0;
	_debug_success_sf = 0;
	_debug_fail_mf = 0;
	_debug_fail_sf = 0;
	_debug_err_mf = 0;
	_debug_err_sf = 0;
	cyg_interrupt_enable();
#endif
		ba_context = BA_CONTEXT_MASTERSHIP_TRANSFER;
#ifdef MVBPROJ_MASTERSHIP_TRANSFER_BLOCKED
		ba_context = BA_CONTEXT_DEVICES_SCAN;
#endif
		
#ifndef MVBPROJ_MASTERSHIP_TRANSFER_BLOCKED
#ifdef MVBPROJ_DEBUG_INFO
	printf("[HANDLE] SVPROCESS, action = BA_CONTEXT_MASTERSHIP_TRANSFER\n");
#endif // ifdef MVBPROJ_DEBUG_INFO
#else
#ifdef MVBPROJ_DEBUG_INFO
	printf("[HANDLE] SVPROCESS, action = BA_CONTEXT_DEVICES_SCAN\n");
#endif // ifdef MVBPROJ_DEBUG_INFO
#endif // ifndef MVBPROJ_MASTERSHIP_TRANSFER_BLOCKED

		bp_number = 0;
	}
	else
	{

#ifndef MVBPROJ_DEFAULT_SCAN_UNIT
		int dsl_c_offset = (bp_number - 1) % 1024;
		if (dsl_c_offset < 512)
		{
			unsigned char *dsl_entry = (unsigned char *)((UNSIGNED32)mvb_administrator.device_scan_list_count0 + ((bp_number - 1) % 1024));
			device_scan_unit = *dsl_entry;
		}
		else
		{
			unsigned char *dsl_entry = (unsigned char *)((UNSIGNED32)mvb_administrator.device_scan_list_count1 + (((bp_number) - 1) % 1024 - 512));
			device_scan_unit = *dsl_entry;
		}
		
#endif // ifndef MVBPROJ_DEFAULT_SCAN_UNIT

#ifdef MVBPROJ_DEFAULT_SCAN_UNIT
		device_scan_unit = MVBPROJ_DEFAULT_SCAN_UNIT;
#endif // ifdef MVBPROJ_DEFAULT_SCAN_UNIT

		if (device_scan_unit > 0)
		{
			ba_context = BA_CONTEXT_DEVICES_SCAN;

			
#ifndef MVBPROJ_DEVICES_SCAN_BLOCKED
#ifdef MVBPROJ_DEBUG_INFO
	printf("[HANDLE] SVPROCESS, action = BA_CONTEXT_DEVICES_SCAN\n");
#endif // ifdef MVBPROJ_DEBUG_INFO
#endif // ifndef MVBPROJ_DEVICES_SCAN_BLOCKED

#ifdef MVBPROJ_DEVICES_SCAN_BLOCKED
			ba_context = BA_CONTEXT_MESSAGE_ARBITRATION;
#ifdef MVBPROJ_DEBUG_INFO
			printf("[HANDLE] SVPROCESS, action = BA_CONTEXT_MESSAGE_ARBITRATION\n");
#endif
#endif

		}
		else
		{
			ba_context = BA_CONTEXT_MESSAGE_ARBITRATION;

#ifdef MVBPROJ_DEBUG_INFO
	printf("[HANDLE] SVPROCESS, action = BA_CONTEXT_MESSAGE_ARBITRATION\n");
#endif
		}
	}

	ba_context_process(0, 0, EXTI_SUPERVISORY_INT_VECTOR);
}

