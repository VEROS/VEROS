//=============================================================================
//
//      main.c
//
//      Main c
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Yinlong Su
// Date:        2012-06-07
// Modified:	2012-11-09
// Description: Main c
// Version:     1.0
//
//####DESCRIPTIONEND####
//
//=============================================================================

#include "main.h"

// Threads: 3 thread
//
// [START ARM]          :: Start ARM program, added on 8th November
//                         - Move 'Refreshing FPGA' to thread can reduce time from 13s to 4s
// [EXTI CONFIGURATION] :: Config EXTI register and attach interrupt
//                         - Any printf call without disabling interrupt may cause breakdown
// [LED SUPPORT]        :: LED twinkle thread

char exti_stack[STACK_SIZE], start_stack[STACK_SIZE];

cyg_thread start_thread_data, exti_thread_data;
cyg_handle_t start_thread_handle, exti_thread_handle;

#ifdef MVBPROJ_LED_SUPPORT

char led_stack[STACK_SIZE];
cyg_thread led_thread_data;
cyg_handle_t led_thread_handle;

#endif // ifdef MVBPROJ_LED_SUPPORT

extern MVB_DEVICE_STATUS mvb_device_status;

/* --------------------------------------------------------------------------
 *  cyg_start
 *
 *  ARM entry function
 *
 *  @param	: void
 *  @return	: void
 *  @see	: start_thread
 *
 *    ARM entry function, start thread.
 * --------------------------------------------------------------------------
 */
void cyg_start(void)
{

#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("\n\n\n\n\nMVB ARM monitor for T113 (build%04d)\n\n", MVB_BUILD_DEFINITION);
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT

#ifdef MVBPROJ_LED_SUPPORT
	mvb_arm_init_led(0);
#endif

	cyg_thread_create(START_WORKTHREAD_PRI, start_thread, 0, "START ARM", &start_stack, STACK_SIZE, &start_thread_handle, &start_thread_data);
    cyg_thread_resume(start_thread_handle);
	cyg_scheduler_start();
}

/* --------------------------------------------------------------------------
 *  start_thread
 *
 *  ARM start thread function
 *
 *  @param	: cyg_addrword_t data
 *  @return	: void
 *  @see	: fpga, parse, create_structure, exti_thread, led_thread
 *
 *  Process:
 *    01. Refresh FPGA;
 *    02. Configure GPIO register;
 *    03. Configure EXTI register;
 *    04. Parse binary file;
 *    05. Create data structure;
 *    06. Attach interrupt;
 *    07. Report device address and data.
 * --------------------------------------------------------------------------
 */
void start_thread(cyg_addrword_t data)
{
	HAL_WRITE_UINT32(CYGARC_REG_SYSTICK_BASE+CYGARC_REG_SYSTICK_RELOAD, 2099 ); 

	cyg_tick_count_t aticks = cyg_current_time();
	if (fpga() == 0)
	{
#ifdef MVBPROJ_BASIC_INFO_SUPPORT
		printf("FPGA init :: ERROR :: ARM STOP\n");
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT
		cyg_thread_exit();
	}
	
	cyg_tick_count_t bticks = cyg_current_time();
	UNSIGNED32 time = ((UNSIGNED32)bticks - (UNSIGNED32)aticks) / 10;
	printf("FPGA init :: PROGRAMMING TIME :: %d ms\n", time);

#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("...configuring GPIO...\n");
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT
	mvb_arm_init_all_gpio();
	
#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("...configuring EXTI...\n");
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT
	mvb_arm_init_exti();

	cyg_thread_create(EXTI_WORKTHREAD_PRI, exti_thread, 0, "EXTI CONFIGURATION", &exti_stack, STACK_SIZE, &exti_thread_handle, &exti_thread_data);
	
	aticks = cyg_current_time();
	if (parse() == 0)
	{
#ifdef MVBPROJ_BASIC_INFO_SUPPORT
		printf("Binary init :: ERROR :: Parsing error, no config data.\n");
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT
	}
	bticks = cyg_current_time();
	time = ((UNSIGNED32)bticks - (UNSIGNED32)aticks) / 10;
	printf("Binary init :: ELAPSED TIME :: %d ms\n", time);
	
#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("...creating data structure...\n");
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT
	create_structure();

#ifdef MVBPROJ_BASIC_INFO_SUPPORT
	printf("...attaching interrupt...\n");
#endif // ifdef MVBPROJ_BASIC_INFO_SUPPORT

#ifdef MVBPROJ_LED_SUPPORT
	cyg_thread_create(LED_WORKTHREAD_PRI, led_thread, 0, "LED SUPPORT", &led_stack, STACK_SIZE, &led_thread_handle, &led_thread_data);
#endif // ifdef MVBPROJ_LED_SUPPORT

    cyg_thread_resume(exti_thread_handle); // Start it

#ifdef MVBPROJ_LED_SUPPORT
	cyg_thread_resume(led_thread_handle);
#endif // ifdef MVBPROJ_LED_SUPPORT

	cyg_thread_exit();
}

#ifdef MVBPROJ_LED_SUPPORT
/* --------------------------------------------------------------------------
 *  led_thread
 *
 *  ARM led thread function
 *
 *  @param	: cyg_addrword_t data
 *  @return	: void
 *
 *  Twinkle the active led
 * --------------------------------------------------------------------------
 */
void led_thread(cyg_addrword_t data)
{
	cyg_uint16 active_light_status = 0;
	while (1)
	{
		mvb_arm_active_led(active_light_status);

		if (mvb_device_status.lat == 1)
		{
#ifdef MVB_ARM_LED_LINE_A
			mvb_arm_line_a_led(active_light_status);
#endif // ifdef MVB_ARM_LED_LINE_A
#ifdef MVB_ARM_LED_LINE_B
			if (mvb_device_status.rld == 1)
			{
				mvb_arm_line_b_led(0);
			}
			else
			{
				mvb_arm_line_b_led(1);
			}
#endif // ifdef MVB_ARM_LED_LINE_B
		}
		else
		{
#ifdef MVB_ARM_LED_LINE_B
			mvb_arm_line_b_led(active_light_status);
#endif // ifdef MVB_ARM_LED_LINE_B
#ifdef MVB_ARM_LED_LINE_A
			if (mvb_device_status.rld == 1)
			{
				mvb_arm_line_a_led(0);
			}
			else
			{
				mvb_arm_line_a_led(1);
			}
#endif // ifdef MVB_ARM_LED_LINE_A
		}
		
		cyg_thread_delay(LED_FREQUENCY);
		if (active_light_status == 0)
			active_light_status = 1;
		else
			active_light_status = 0;
	}
}
#endif // ifdef MVBPROJ_LED_SUPPORT