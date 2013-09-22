//=============================================================================
//
//      intr.c
//
//      Interrupt C file
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Yinlong Su
// Date:        2012-06-07
// Modified:	2012-11-09
// Description: Interrupt C file
// Version:     1.0
//
//####DESCRIPTIONEND####
//
//=============================================================================

#include "intr.h"

//=============================================================================
// Variable Description
//
// bool wait_for_ba	:: When there is no main frame on MVB bus for 1.3ms,
//                     this flag turn to TRUE. All backup administrator
//                     will be counting T_standby to become current
//                     master. When receving valid main frame, this flag
//                     turn FALSE, telling those backup administrator which
//                     are waiting for T_standby to exit standup thread.
//
// cyg_uint32 frame_checkbit :: Enum type. Identify frame type as
//                              HAL_IO_ENUM_MAIN_FRAME or
//                              HAL_IO_ENUM_SLAVE_FRAME
//
// cyg_uint32 sync_checkbit  :: Enum type. Identify sync type as
//                              HAL_IO_ENUM_SYNC_STATUS or
//                              HAL_IO_ENUM_SYNC_ADDRESS
//
// UNSIGNED16 current_mf, last_mf :: Record current and last main frame data.
// UNSIGNED16 current_sf, last_sf :: Record current and last slave frame data.
bool		wait_for_ba;

cyg_uint32	frame_checkbit, sync_checkbit, sync_interrupt_flag;
UNSIGNED16	current_mf, last_mf;
UNSIGNED16	current_sf, last_sf;



// Thread:
//
// [STANDUP THREAD] :: When there is no main frame on MVB bus for 1.3ms, standup thread start and count
//                     silence time T, stand up if there is no master during this time.
char standup_stack[SA_STACK_SIZE];

cyg_thread		standup_thread_data;
cyg_handle_t	standup_thread_handle;
int standup_flag = 0;


extern UNSIGNED16 this_akey;
extern UNSIGNED16 this_addr;
extern MVB_ADMINISTRATOR mvb_administrator;
extern MVB_DEVICE_STATUS mvb_device_status;
extern cyg_uint16 mvb_device_status_16;
extern UNSIGNED16 ba_mf;

cyg_handle_t     standup_counter_handle;

cyg_tick_count_t standup_alarm_count;
cyg_alarm        standup_alarm_object;
cyg_handle_t     standup_alarm_handle;

extern int md_notime;

#ifdef MVBPROJ_DEBUG_REALTIME

int _debug_success_mf = 0, _debug_success_sf = 0;
int _debug_fail_mf = 0, _debug_fail_sf = 0;
int _debug_err_mf = 0, _debug_err_sf = 0;
int _debug_sync = 0;

#endif

#ifdef MVBPROJ_DEBUG_CONN_BA
extern int bp_number;
extern int _conn_ba_flag;
extern UNSIGNED8 ba_context;
#endif

/* --------------------------------------------------------------------------
 *  exti_thread
 *
 *  EXTI configuration thread function
 *
 *  @param	: cyg_addrword_t data
 *  @return	: void
 *
 *  Interrupt ISR and DSR:
 *    01. Supervisory interrupt ISR;
 *    02. Timeout interrupt ISR and DSR;
 *    03. Error frame interrupt ISR and DSR;
 *    04. Main frame interrupt ISR;
 *    05. Slave frame interrupt ISR;
 *    06. Sync interrupt ISR and DSR;
 *    07. No time interrupt ISR.
 *
 *  Process:
 *    01. Create, configure and attach interrupt ISR and DSR;
 *    02. Unmask the interrupt vector;
 *    03. Display information;
 *    04. Enable all interrupt;
 *    05. Synchronize device status.
 * --------------------------------------------------------------------------
 */
void exti_thread(cyg_addrword_t data)
{

	cyg_interrupt	supervisory_interrupt,
					timeout_interrupt,
					errorframe_interrupt,
					mainframe_interrupt,
					slaveframe_interrupt,
					sync_interrupt,
					notime_interrupt;
	cyg_handle_t	supervisory_interrupt_handle,
					timeout_interrupt_handle,
					errorframe_interrupt_handle,
					mainframe_interrupt_handle,
					slaveframe_interrupt_handle,
					sync_interrupt_handle,
					notime_interrupt_handle;

	cyg_interrupt_create(EXTI_SUPERVISORY_INT_VECTOR, EXTI_SUPERVISORY_INT_PRI, 0, supervisory_interrupt_isr, supervisory_interrupt_dsr, &supervisory_interrupt_handle, &supervisory_interrupt);
	cyg_interrupt_configure(EXTI_SUPERVISORY_INT_VECTOR, 0, 0);
	cyg_interrupt_attach(supervisory_interrupt_handle);

	cyg_interrupt_create(EXTI_TIMEOUT_VECTOR, EXTI_TIMEOUT_PRI, 0, timeout_interrupt_isr, timeout_interrupt_dsr, &timeout_interrupt_handle, &timeout_interrupt);
	cyg_interrupt_configure(EXTI_TIMEOUT_VECTOR, 0, 0);
	cyg_interrupt_attach(timeout_interrupt_handle);

	cyg_interrupt_create(EXTI_ERROR_FRAME_VECTOR, EXTI_ERROR_FRAME_PRI, 0, errorframe_interrupt_isr, errorframe_interrupt_dsr, &errorframe_interrupt_handle, &errorframe_interrupt);
	cyg_interrupt_configure(EXTI_ERROR_FRAME_VECTOR, 0, 0);
	cyg_interrupt_attach(errorframe_interrupt_handle);

	cyg_interrupt_create(EXTI_MAIN_FRAME_VECTOR, EXTI_MAIN_FRAME_PRI, 0, mainframe_interrupt_isr, mainframe_interrupt_dsr, &mainframe_interrupt_handle, &mainframe_interrupt);
	cyg_interrupt_configure(EXTI_MAIN_FRAME_VECTOR, 0, 0);
	cyg_interrupt_attach(mainframe_interrupt_handle);

	cyg_interrupt_create(EXTI_SLAVE_FRAME_VECTOR, EXTI_SLAVE_FRAME_PRI, 0, slaveframe_interrupt_isr, slaveframe_interrupt_dsr, &slaveframe_interrupt_handle, &slaveframe_interrupt);
	cyg_interrupt_configure(EXTI_SLAVE_FRAME_VECTOR, 0, 0);
	cyg_interrupt_attach(slaveframe_interrupt_handle);

	cyg_interrupt_create(EXTI_SYNC_VECTOR, EXTI_SYNC_PRI, 0, sync_interrupt_isr, sync_interrupt_dsr, &sync_interrupt_handle, &sync_interrupt);
	cyg_interrupt_configure(EXTI_SYNC_VECTOR, 0, 0);
	cyg_interrupt_attach(sync_interrupt_handle);

	cyg_interrupt_create(EXTI_NO_TIME_VECTOR, EXTI_NO_TIME_PRI, 0, notime_interrupt_isr, notime_interrupt_dsr, &notime_interrupt_handle, &notime_interrupt);
	cyg_interrupt_configure(EXTI_NO_TIME_VECTOR, 0, 0);
	cyg_interrupt_attach(notime_interrupt_handle);



#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("Interrupt init :: attach completed\n\n");
	printf("Device address: 0x%04x (%d), status: 0x%04x, All clear.\n", this_addr, this_addr, mvb_device_status_16);
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT

	cyg_interrupt_unmask(EXTI_SUPERVISORY_INT_VECTOR);
	cyg_interrupt_unmask(EXTI_TIMEOUT_VECTOR);
	cyg_interrupt_unmask(EXTI_ERROR_FRAME_VECTOR);
	cyg_interrupt_unmask(EXTI_MAIN_FRAME_VECTOR);
	cyg_interrupt_unmask(EXTI_SLAVE_FRAME_VECTOR);
	cyg_interrupt_unmask(EXTI_SYNC_VECTOR);
	cyg_interrupt_unmask(EXTI_NO_TIME_VECTOR);
	cyg_interrupt_enable();

	mvb_arm_send_status(mvb_device_status_16);

	cyg_thread_exit();
}

/* --------------------------------------------------------------------------
 *  standup_alarm
 *
 *  Master timeout standup alarm function
 *
 *  @param	: cyg_handle_t   alarm
 *            cyg_addrword_t data
 *  @return	: void
 *
 *  Become current master.
 * --------------------------------------------------------------------------
 */
void standup_alarm(cyg_handle_t alarm, cyg_addrword_t data)
{
	if (wait_for_ba)
		ba_init(true);
	cyg_thread_kill(standup_thread_handle);
	cyg_alarm_delete(standup_alarm_handle);
	standup_flag = 0;
}

/* --------------------------------------------------------------------------
 *  standup_thread
 *
 *  Master timeout standup thread function
 *
 *  @param	: cyg_addrword_t data
 *  @return	: void
 *
 *  Count silence time, stand up if there is no master.
 * --------------------------------------------------------------------------
 */
void standup_thread(cyg_addrword_t data)
{
	standup_flag = 1;
/*
	cyg_tick_count_t mainticks = cyg_current_time();
	cyg_tick_count_t slaveticks;
	while (wait_for_ba)
	{
		slaveticks = cyg_current_time();
		if ((UNSIGNED32)slaveticks - (UNSIGNED32)mainticks > this_addr)
		{
			ba_init(true);
			break;

		}
	}
	standup_flag = 0;
	cyg_interrupt_unmask(EXTI_TIMEOUT_VECTOR);
	cyg_thread_exit();
	*/

	cyg_clock_to_counter(cyg_real_time_clock(), &standup_counter_handle);

	standup_alarm_count = 26 * (this_addr + 15) - 13;


	cyg_alarm_create(standup_counter_handle, standup_alarm, 0, &standup_alarm_handle, &standup_alarm_object);
	cyg_alarm_initialize(standup_alarm_handle, cyg_current_time() + standup_alarm_count, standup_alarm_count);
	cyg_alarm_enable(standup_alarm_handle);

	while (1)
	{
		cyg_thread_delay(10000);
	}
	//cyg_thread_exit();
}


/* --------------------------------------------------------------------------
 *  supervisory_interrupt_isr
 *
 *  Supervisory phase interrupt ISR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_addrword_t	data
 *  @return		: cyg_uint32
 *  @trigger	: hardware interrupt (FPGA signal BSP)
 *  @condition	: current master
 *  @see		: supervisory_interrupt_handle
 *
 *  Supervisory phase interrupt ISR
 *
 * --------------------------------------------------------------------------
 */
cyg_uint32 supervisory_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data)
{
	cyg_interrupt_mask(vector);
	cyg_interrupt_acknowledge(vector);

#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] SUPERVISORY_INTERRUPT_ISR\n");
#endif

	md_notime = 0;
	supervisory_interrupt_handle();
	cyg_interrupt_unmask(vector);
	return (CYG_ISR_HANDLED);
}

/* --------------------------------------------------------------------------
 *  supervisory_interrupt_dsr
 *
 *  Supervisory phase interrupt DSR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_ucount32		count
 *                cyg_addrword_t	data
 *  @return		: void
 *  @trigger	: hardware interrupt (FPGA signal BSP)
 *  @condition	: current master
 *
 *  Supervisory phase interrupt DSR
 *
 * --------------------------------------------------------------------------
 */
void supervisory_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data)
{
#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] SUPERVISORY_INTERRUPT_DSR\n");
#endif

	cyg_interrupt_unmask(vector);
}

/* --------------------------------------------------------------------------
 *  timeout_interrupt_isr
 *
 *  Timeout interrupt ISR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_addrword_t	data
 *  @return		: cyg_uint32
 *  @trigger	: hardware interrupt (FPGA signal frame timeout)
 *
 *  Timeout interrupt ISR
 *
 * --------------------------------------------------------------------------
 */
cyg_uint32 timeout_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data)
{
	cyg_interrupt_mask(vector);
	cyg_interrupt_acknowledge(vector);

	HAL_IO_FRAME_CHECKBIT(&frame_checkbit);

#ifdef MVBPROJ_DEBUG_INFO
	diag_printf("[EXTI] TIMEOUT_INTERRUPT_ISR\n");
#endif

	return (CYG_ISR_HANDLED | CYG_ISR_CALL_DSR);
}

/* --------------------------------------------------------------------------
 *  timeout_interrupt_dsr
 *
 *  Timeout interrupt DSR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_ucount32		count
 *                cyg_addrword_t	data
 *  @return		: void
 *  @trigger	: hardware interrupt (FPGA signal frame timeout)
 *  @see		: standup_thread, build_list_of_devices_scan
 *
 *  Timeout interrupt DSR
 *
 * --------------------------------------------------------------------------
 */
void timeout_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data)
{
#ifdef MVBPROJ_DEBUG_INFO
	diag_printf("[EXTI] TIMEOUT_INTERRUPT_DSR\n");
#endif
	if (frame_checkbit == HAL_IO_ENUM_MAIN_FRAME)
	{
#ifdef MVBPROJ_DEBUG_REALTIME
	_debug_fail_mf++;
#endif
		wait_for_ba = true;

		if (mvb_device_status.ba == 1 && standup_flag == 0 && mvb_device_status.cs3 == 0)
		{
			standup_flag = 1;
			cyg_thread_create(SA_WORKTHREAD_PRI, standup_thread, 0, "STANDUP THREAD", &standup_stack, SA_STACK_SIZE, &standup_thread_handle, &standup_thread_data);
			cyg_thread_resume(standup_thread_handle); // Start it
		}
	}
	else
	{

#ifdef MVBPROJ_DEBUG_REALTIME
	_debug_fail_sf++;
#endif

		if (mvb_device_status.cs3 == 0) // MAS
		{
			if (mvb_device_status.ba == 1)
			{
				//modify by lqc
				//build_list_of_devices_scan(FRAME_ADDRESS(current_mf), 0, false);
			}
		}
		else
		{
			ba_context_process(0, 0, vector);
		}
	}
	cyg_interrupt_unmask(vector);
}

/* --------------------------------------------------------------------------
 *  error_interrupt_isr
 *
 *  Error frame interrupt ISR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_addrword_t	data
 *  @return		: cyg_uint32
 *  @trigger	: hardware interrupt (FPGA signal frame error)
 *
 *  Error frame interrupt ISR
 *
 * --------------------------------------------------------------------------
 */
cyg_uint32 errorframe_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data)
{
	cyg_interrupt_mask(vector);
	cyg_interrupt_acknowledge(vector);

#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] ERRORFRAME_INTERRUPT_ISR\n");
#endif

	HAL_IO_FRAME_CHECKBIT(&frame_checkbit);

	return (CYG_ISR_HANDLED | CYG_ISR_CALL_DSR);
}

/* --------------------------------------------------------------------------
 *  error_interrupt_dsr
 *
 *  Error frame interrupt DSR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_ucount32		count
 *                cyg_addrword_t	data
 *  @return		: void
 *  @trigger	: hardware interrupt (FPGA signal frame error)
 *  @see		: standup_thread, build_list_of_devices_scan
 *
 *  Error frame interrupt DSR
 *
 * --------------------------------------------------------------------------
 */
void errorframe_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data)
{
#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] ERRORFRAME_INTERRUPT_DSR\n");
#endif
	if (frame_checkbit == HAL_IO_ENUM_MAIN_FRAME)
	{
#ifdef MVBPROJ_DEBUG_REALTIME
	_debug_err_mf++;
#endif // ifdef MVBPROJ_DEBUG_REALTIME
		if (mvb_device_status.cs3 == 1)
		{
			mvb_device_status.cs3 = 0;
			mvb_device_status_16 = *((cyg_uint16*)&mvb_device_status);

#ifdef MVBPROJ_DEBUG_INFO
	printf("\t[BA] conflict\n");
	printf("SED SYNC.\n");
#endif
#ifdef MVBPROJ_LED_SUPPORT
	mvb_arm_master_led(0);
#endif
			mvb_arm_send_status(mvb_device_status_16);
		}
	}
	else
	{
#ifdef MVBPROJ_DEBUG_REALTIME
	_debug_err_sf++;
#endif // ifdef MVBPROJ_DEBUG_REALTIME

	}
	cyg_interrupt_unmask(vector);
}


/* --------------------------------------------------------------------------
 *  mainframe_interrupt_isr
 *
 *  Main frame interrupt ISR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_addrword_t	data
 *  @return		: cyg_uint32
 *  @trigger	: hardware interrupt (FPGA signal main frame receive)
 *  @see		: mfprocess_handle
 *
 *  Main frame interrupt ISR
 *
 * --------------------------------------------------------------------------
 */
cyg_uint32 mainframe_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data)
{
	cyg_interrupt_mask(vector);
	cyg_interrupt_acknowledge(vector);

#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] MAINFRAME_INTERRUPT_ISR\n");
#endif

	wait_for_ba = false;
	last_mf = current_mf;
	mvb_arm_receive_frame(current_mf);

	/*
	cyg_interrupt_disable();
	printf("rev m_frame 0x%04x\n", current_mf);
	cyg_interrupt_enable();
	*/
	if (mvb_device_status.cs3 == 1 && current_mf != ba_mf)
	{

		mvb_device_status.cs3 = 0;
		mvb_device_status_16 = *((cyg_uint16*)&mvb_device_status);

#ifdef MVBPROJ_DEBUG_INFO
	printf("BA conflict, mf: 0x%04x, ba: 0x%04x\n", current_mf, ba_mf);
	printf("SED SYNC.\n");
#endif
#ifdef MVBPROJ_LED_SUPPORT
	mvb_arm_master_led(0);
#endif
		mvb_arm_send_status(mvb_device_status_16);
	}

#ifdef MVBPROJ_DEBUG_REALTIME
	_debug_success_mf++;
#endif
#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] MAINFRAME_INTERRUPT_DSR MF:0x%04x\n", current_mf);
#endif


	mfprocess_handle(vector);
	cyg_interrupt_unmask(vector);
	return (CYG_ISR_HANDLED);
}

/* --------------------------------------------------------------------------
 *  mainframe_interrupt_dsr
 *
 *  Main frame interrupt DSR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_ucount32		count
 *                cyg_addrword_t	data
 *  @return		: void
 *  @trigger	: hardware interrupt (FPGA signal main frame receive)
 *
 *  Main frame interrupt DSR
 *
 * --------------------------------------------------------------------------
 */
void mainframe_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data)
{
	cyg_interrupt_unmask(vector);
}

/* --------------------------------------------------------------------------
 *  slaveframe_interrupt_isr
 *
 *  Slave frame interrupt ISR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_addrword_t	data
 *  @return		: cyg_uint32
 *  @trigger	: hardware interrupt (FPGA signal slave frame receive)
 *  @see		: sfprocess_handle
 *
 *  Slave frame interrupt ISR
 *
 * --------------------------------------------------------------------------
 */
cyg_uint32 slaveframe_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data)
{
	cyg_interrupt_mask(vector);
	cyg_interrupt_acknowledge(vector);

#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] SLAVEFRAME_INTERRUPT_ISR\n");
#endif

	last_sf = current_sf;
	mvb_arm_receive_frame(current_sf);
	/*
	cyg_interrupt_disable();
	printf("rev s_frame 0x%04x\n", current_sf);
	cyg_interrupt_enable();
	*/

#ifdef MVBPROJ_DEBUG_REALTIME
	_debug_success_sf++;
#endif
#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] SLAVEFRAME_INTERRUPT_DSR SF:0x%04x\n", current_sf);
#endif

	sfprocess_handle(vector);
	cyg_interrupt_unmask(vector);
	return (CYG_ISR_HANDLED);
}

/* --------------------------------------------------------------------------
 *  slaveframe_interrupt_dsr
 *
 *  Slave frame interrupt DSR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_ucount32		count
 *                cyg_addrword_t	data
 *  @return		: void
 *  @trigger	: hardware interrupt (FPGA signal slave frame receive)
 *
 *  Slave frame interrupt DSR
 *
 * --------------------------------------------------------------------------
 */
void slaveframe_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data)
{
	cyg_interrupt_unmask(vector);
}

/* --------------------------------------------------------------------------
 *  sync_interrupt_isr
 *
 *  Synchronization interrupt ISR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_addrword_t	data
 *  @return		: cyg_uint32
 *  @trigger	: hardware interrupt (FPGA signal synchronization)
 *
 *  Synchronization interrupt ISR
 *
 * --------------------------------------------------------------------------
 */
cyg_uint32 sync_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data)
{
	cyg_interrupt_mask(vector);
	cyg_interrupt_acknowledge(vector);
	HAL_IO_SYNC_CHECKBIT(&sync_checkbit);

#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] SYNC_INTERRUPT_ISR\n");
#endif

	return (CYG_ISR_HANDLED | CYG_ISR_CALL_DSR);
}

/* --------------------------------------------------------------------------
 *  sync_interrupt_dsr
 *
 *  Synchronization interrupt DSR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_ucount32		count
 *                cyg_addrword_t	data
 *  @return		: void
 *  @trigger	: hardware interrupt (FPGA signal synchronization)
 *  @see		: syncprocess_handle
 *
 *  Synchronization interrupt DSR
 *
 * --------------------------------------------------------------------------
 */
void sync_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data)
{

#ifdef MVBPROJ_DEBUG_REALTIME
	_debug_sync++;
#endif
	syncprocess_handle();
	cyg_interrupt_unmask(vector);
}

/* --------------------------------------------------------------------------
 *  notime_interrupt_isr
 *
 *  No time interrupt ISR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_addrword_t	data
 *  @return		: cyg_uint32
 *  @trigger	: hardware interrupt (FPGA signal no time)
 *  @condition	: current master
 *
 *  No time interrupt ISR
 *
 * --------------------------------------------------------------------------
 */
cyg_uint32 notime_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data)
{
	cyg_interrupt_mask(vector);
	cyg_interrupt_acknowledge(vector);
	md_notime = 1;
#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] NOTIME_INTERRUPT_ISR\n");
#endif
	cyg_interrupt_unmask(vector);
	return (CYG_ISR_HANDLED);
}

/* --------------------------------------------------------------------------
 *  notime_interrupt_dsr
 *
 *  No time interrupt DSR
 *
 *  @param		: cyg_vector_t		vector
 *                cyg_ucount32		count
 *                cyg_addrword_t	data
 *  @return		: cyg_uint32
 *  @trigger	: hardware interrupt (FPGA signal no time)
 *  @condition	: current master
 *
 *  No time interrupt DSR
 *
 * --------------------------------------------------------------------------
 */
void notime_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data)
{
#ifdef MVBPROJ_DEBUG_INFO
	printf("[EXTI] NOTIME_INTERRUPT_DSR\n");
#endif
	cyg_interrupt_unmask(vector);
}

/* --------------------------------------------------------------------------
 *  mfprocess_handle
 *
 *  Main frame multiple interrupts process handle
 *
 *  @param		: cyg_vector_t vector
 *  @return		: void
 *  @trigger	: ISR called
 *
 *  Main frame multiple interrupts process handle
 *
 * --------------------------------------------------------------------------
 */
void mfprocess_handle(cyg_vector_t vector)
{

/*
if (FRAME_ADDRESS(current_mf) == this_addr)
{
	switch (FRAME_F_CODE(current_mf))
	{
	case FRAME_F_CODE_8:
		if (mvb_device_status.ba == 1)
		{
			if (mvb_device_status.cs2 == 1)
			{
				mvb_arm_send_slave_frame(0x8000 | this_akey);
				ba_init(true);
			}
			else
			{
				mvb_arm_send_slave_frame(0x0000);
			}
		}
		break;
	case FRAME_F_CODE_15:
		mvb_arm_send_slave_frame(mvb_device_status_16);
		break;
	}
}
*/
	sync_interrupt_flag = 1;
#ifdef MVBPROJ_DEBUG_INFO
	printf("[HANDLE] MFPROCESS MF:0x%04x\n", current_mf);
#endif
	switch (FRAME_F_CODE(current_mf))
		{
		case FRAME_F_CODE_8:
			if (mvb_device_status.ba == 1 && FRAME_ADDRESS(current_mf) == this_addr)
			{
				mvb_arm_send_slave_frame(0x8000 | this_akey);
				ba_init(true);
			}
		break;
	case FRAME_F_CODE_15:
		if (FRAME_ADDRESS(current_mf) == this_addr)
		{
#ifdef MVBPROJ_DEBUG_INFO
	printf("[HANDLE] MFPROCESS, sending status, F=15 Status=0x%04x\n", mvb_device_status_16);
#endif
			mvb_arm_send_slave_frame(mvb_device_status_16);
		}
		break;
	case FRAME_F_CODE_9:
		Fcode_9_handler();
		break;
	case FRAME_F_CODE_13:
		Fcode_13_handler();
		break;
	case FRAME_F_CODE_14:
		Fcode_14_handler();
		break;
	case FRAME_F_CODE_12:
		Fcode_12_handler();
		break;

	}

}

/* --------------------------------------------------------------------------
 *  sfprocess_handle
 *
 *  Slave frame multiple interrupts process handle
 *
 *  @param		: cyg_vector_t vector
 *  @return		: void
 *  @trigger	: ISR called
 *  @see		: build_list_of_devices_scan, ba_context_process
 *
 *  Slave frame multiple interrupts process handle
 *
 * --------------------------------------------------------------------------
 */
void sfprocess_handle(cyg_vector_t vector)
{
	sync_interrupt_flag = 1;
#ifdef MVBPROJ_DEBUG_INFO
	printf("[HANDLE] SFPROCESS SF:0x%04x\n", current_sf);
#endif

	if (mvb_device_status.cs3 == 0)
	{
		if (mvb_device_status.ba == 1)
		{
			switch (FRAME_F_CODE(current_mf))
			{
			case FRAME_F_CODE_15:
				//modify by lqc
				//build_list_of_devices_scan(FRAME_ADDRESS(current_mf), current_sf, false);
				break;
			}
		}
	}
	else
	{
		ba_context_process(FRAME_F_CODE(current_mf), current_sf, vector);
	}
}

/* --------------------------------------------------------------------------
 *  syncprocess_handle
 *
 *  Synchronization interrupt process handle
 *
 *  @param		: void
 *  @return		: void
 *  @trigger	: DSR called
 *  @see		: build_list_of_devices_scan
 *
 *  Synchronization interrupt process handle
 *
 * --------------------------------------------------------------------------
 */
void syncprocess_handle()
{
	if (sync_checkbit == HAL_IO_ENUM_SYNC_STATUS)
	{
		cyg_uint16 new_status_16;
		sync_interrupt_flag = 0;
		mvb_arm_receive_sync(new_status_16);
		MVB_DEVICE_STATUS new_status = *((MVB_DEVICE_STATUS*)&new_status_16);

		if ((sync_interrupt_flag == 0) && (STATUS_CHECK(new_status_16) == 0))
		{
			mvb_device_status_16 = new_status_16;
			mvb_device_status = new_status;
#ifdef MVBPROJ_DEBUG_INFO
			printf("[EXTI] SYNC_INTERRUPT_DSR, Status = 0x%04x\n", mvb_device_status_16);
#endif

			if (mvb_device_status.ba == 0 || mvb_device_status.cs3 == 0)
			{
#ifdef MVBPROJ_LED_SUPPORT
				mvb_arm_master_led(0);
#endif
			}
		}
#ifdef MVBPROJ_DEBUG_SYNC
cyg_interrupt_disable();
printf("[EXTI] SYNC_INTERRUPT_DSR, Status = 0x%04x\n", mvb_device_status_16);
cyg_interrupt_enable();
#endif // ifdef MVBPROJ_DEBUG_SYNC
	}
	else
	{
		cyg_uint16 content;
		sync_interrupt_flag = 0;
		mvb_arm_receive_sync(content);

		if (sync_interrupt_flag == 0)
		{
			//modify by lqc
			//build_list_of_devices_scan(this_addr, 0, true);
			this_addr = FRAME_ADDRESS(content);
			//modify by lqc
			//build_list_of_devices_scan(this_addr, mvb_device_status_16, false);

			standup_alarm_count = 26 * (this_addr + 15) - 13;

			if (((content >> 13) % 2) == 0 && mvb_device_status.ba == 1)
			{
				mvb_device_status.ba = 0;
				mvb_device_status.cs2 = 0;
				mvb_device_status.cs3 = 0;
				mvb_device_status_16 = *((cyg_uint16*)&mvb_device_status);
#ifdef MVBPROJ_LED_SUPPORT
		mvb_arm_master_led(0);
#endif
			}
			else if (((content >> 13) % 2) == 1 && mvb_device_status.ba == 0)
			{
				mvb_device_status.ba = 1;
				mvb_device_status.cs2 = 1;
				mvb_device_status_16 = *((cyg_uint16*)&mvb_device_status);
			}
#ifdef MVBPROJ_DEBUG_INFO
			printf("[EXTI] SYNC_INTERRUPT_DSR, Address = 0x%04x\n", content);
#endif
#ifdef MVBPROJ_DEBUG_SYNC
cyg_interrupt_disable();
printf("[EXTI] SYNC_INTERRUPT_DSR, Address = 0x%04x\n", content);
cyg_interrupt_enable();
#endif // ifdef MVBPROJ_DEBUG_SYNC
		}
	}
	if (STATUS_CHECK(mvb_device_status_16) == 0)
		mvb_arm_send_status(mvb_device_status_16);

}
