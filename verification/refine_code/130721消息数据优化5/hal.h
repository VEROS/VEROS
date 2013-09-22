#ifndef MVBONCE_HAL_H
#define MVBONCE_HAL_H
//=============================================================================
//
//      hal.h
//
//      ARM Pin configuration, GPIO definitions and EXTI configuration
//      Macros for hardware abstraction layer calls
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Yinlong Su
// Date:        2012-08-16
// Modified:	2012-11-09
// Description: ARM GPIO/EXTI configuration and hardware functions,
//              macros for hardware abstraction layer calls
// Version:     0.7A
// Usage:       #include "hal.h"
//
//####DESCRIPTIONEND####
//
//=============================================================================

#include "mvb_project.h"
#include <cyg/kernel/kapi.h>
#include <pkgconf/system.h>
#include <cyg/hal/var_io.h>

#define IO_RESET	0x00000000
#define HAL_DELAY_COUNT	0x00

//=============================================================================
// LED pin configuration
//
//	* STM3240G-EVAL
//	+======+=====+
//	| LED1 | PG6 |
//	| LED2 | PG8 |
//	| LED3 | PI9 |
//	| LED4 | PC7 |
//	+======+=====+
//
//  * MVB V4, MVB V7A
//	+======+======+========+====+
//	| LED1 | PF11 | ACTIVE | D3 |
//	| LED2 |  PB0 | MASTER | D4 |
//	+======+======+========+====+
//
//  * MVB V8
//	+======+======+========+=====+
//	| LED1 | PB10 | ACTIVE | R12 |
//	| LED2 | PB12 | MASTER | P12 |
//	| LED3 | PB14 | MASTER | R14 |
//	| LED4 | PB15 | MASTER | R15 |
//	+======+======+========+=====+
#ifdef MVBPROJ_LED_SUPPORT

#ifdef MVBPROJ_HAL_IO_V1
#define	MVB_ARM_LED1	( CYGHWR_HAL_STM32_PIN_OUT(G, 6, PUSHPULL, NONE, AT_LEAST(50)) )
#define	MVB_ARM_LED2	( CYGHWR_HAL_STM32_PIN_OUT(G, 8, PUSHPULL, NONE, AT_LEAST(50)) )
#define MVB_ARM_LED3	( CYGHWR_HAL_STM32_PIN_OUT(I, 9, PUSHPULL, NONE, AT_LEAST(50)) )
#define	MVB_ARM_LED4	( CYGHWR_HAL_STM32_PIN_OUT(C, 7, PUSHPULL, NONE, AT_LEAST(50)) )
#endif // ifdef MVBPROJ_HAL_IO_V1

#ifdef MVBPROJ_HAL_IO_V4
#define	MVB_ARM_LED1 ( CYGHWR_HAL_STM32_PIN_OUT(F, 11, PUSHPULL, NONE, AT_LEAST(50)) )
#define	MVB_ARM_LED2 ( CYGHWR_HAL_STM32_PIN_OUT(B,  0, PUSHPULL, NONE, AT_LEAST(50)) )

#define MVB_ARM_LED_ACTIVE	MVB_ARM_LED1
#define MVB_ARM_LED_MASTER	MVB_ARM_LED2
#endif // ifdef MVBPROJ_HAL_IO_V4

#ifdef MVBPROJ_HAL_IO_V7A
#define	MVB_ARM_LED1 ( CYGHWR_HAL_STM32_PIN_OUT(F, 11, PUSHPULL, NONE, AT_LEAST(50)) )
#define	MVB_ARM_LED2 ( CYGHWR_HAL_STM32_PIN_OUT(B,  0, PUSHPULL, NONE, AT_LEAST(50)) )

#define MVB_ARM_LED_ACTIVE	MVB_ARM_LED1
#define MVB_ARM_LED_MASTER	MVB_ARM_LED2
#endif // ifdef MVBPROJ_HAL_IO_V7A

#ifdef MVBPROJ_HAL_IO_V8
#define	MVB_ARM_LED1 ( CYGHWR_HAL_STM32_PIN_OUT(B, 10, PUSHPULL, NONE, AT_LEAST(50)) )
#define	MVB_ARM_LED2 ( CYGHWR_HAL_STM32_PIN_OUT(B, 12, PUSHPULL, NONE, AT_LEAST(50)) )
#define	MVB_ARM_LED3 ( CYGHWR_HAL_STM32_PIN_OUT(B, 14, PUSHPULL, NONE, AT_LEAST(50)) )
#define	MVB_ARM_LED4 ( CYGHWR_HAL_STM32_PIN_OUT(B, 15, PUSHPULL, NONE, AT_LEAST(50)) )

#define MVB_ARM_LED_ACTIVE	MVB_ARM_LED1
#define MVB_ARM_LED_MASTER	MVB_ARM_LED2
#define MVB_ARM_LED_LINE_A	MVB_ARM_LED3
#define MVB_ARM_LED_LINE_B	MVB_ARM_LED4
#endif // ifdef MVBPROJ_HAL_IO_V8

#define	MVB_ARM_LED_SET(__led, __flag) CYGHWR_HAL_STM32_GPIO_OUT(__led, __flag);
#endif // ifdef MVBPROJ_LED_SUPPORT


//=============================================================================
// GPIO register address
#define GPIO_A_BASE	0x40020000
#define GPIO_B_BASE	0x40020400
#define GPIO_C_BASE 0x40020800
#define GPIO_D_BASE 0x40020C00
#define GPIO_E_BASE 0x40021000
#define GPIO_F_BASE 0x40021400
#define GPIO_G_BASE 0x40021800
#define GPIO_H_BASE	0x40021C00
#define GPIO_I_BASE 0x40022000

#define GPIO_IDR_OFFSET	0x010
#define GPIO_ODR_OFFSET	0x014

#define GPIO_A_IDR	(GPIO_A_BASE + GPIO_IDR_OFFSET)
#define GPIO_B_IDR	(GPIO_B_BASE + GPIO_IDR_OFFSET)
#define GPIO_C_IDR	(GPIO_C_BASE + GPIO_IDR_OFFSET)
#define GPIO_D_IDR	(GPIO_D_BASE + GPIO_IDR_OFFSET)
#define GPIO_E_IDR	(GPIO_E_BASE + GPIO_IDR_OFFSET)
#define GPIO_F_IDR	(GPIO_F_BASE + GPIO_IDR_OFFSET)
#define GPIO_G_IDR	(GPIO_G_BASE + GPIO_IDR_OFFSET)
#define GPIO_H_IDR	(GPIO_H_BASE + GPIO_IDR_OFFSET)
#define GPIO_I_IDR	(GPIO_I_BASE + GPIO_IDR_OFFSET)

#define GPIO_A_ODR	(GPIO_A_BASE + GPIO_ODR_OFFSET)
#define GPIO_B_ODR	(GPIO_B_BASE + GPIO_ODR_OFFSET)
#define GPIO_C_ODR	(GPIO_C_BASE + GPIO_ODR_OFFSET)
#define GPIO_D_ODR	(GPIO_D_BASE + GPIO_ODR_OFFSET)
#define GPIO_E_ODR	(GPIO_E_BASE + GPIO_ODR_OFFSET)
#define GPIO_F_ODR	(GPIO_F_BASE + GPIO_ODR_OFFSET)
#define GPIO_G_ODR	(GPIO_G_BASE + GPIO_ODR_OFFSET)
#define GPIO_H_ODR	(GPIO_H_BASE + GPIO_ODR_OFFSET)
#define GPIO_I_ODR	(GPIO_I_BASE + GPIO_ODR_OFFSET)

//=============================================================================
// GPIO Group Define
//
// + Note:
//
//   - Version 1
//   Control Group 	:	GPIO A
//   Data Group		:	GPIO B
//   Interrupt Group:	GPIO H
//
//   - Version 4
//   Control Group	:	GPIO C
//   Data Group		:	GPIO A
//   Interrupt Group:	GPIO B + GPIO E + GPIO H
//
//   - Version 7A
//   Control Group	:	GPIO C
//   Data Group		:	GPIO A
//   Interrupt Group:	GPIO F + GPIO G
//
//   - Version 8
//   Control Group	:	GPIO C
//   Data Group		:	GPIO A
//   Interrupt Group:	GPIO G

#ifdef MVBPROJ_HAL_IO_V1

#define GPIO_CONTROL_GROUP_IDR	GPIO_A_IDR
#define GPIO_CONTROL_GROUP_ODR	GPIO_A_ODR
#define GPIO_DATA_GROUP_IDR		GPIO_B_IDR
#define GPIO_DATA_GROUP_ODR		GPIO_B_ODR

#endif // ifdef MVBPROJ_HAL_IO_V1

#ifdef MVBPROJ_HAL_IO_V4

#define GPIO_CONTROL_GROUP_IDR	GPIO_C_IDR
#define GPIO_CONTROL_GROUP_ODR	GPIO_C_ODR
#define GPIO_DATA_GROUP_IDR		GPIO_A_IDR
#define GPIO_DATA_GROUP_ODR		GPIO_A_ODR

#endif // ifdef MVBPROJ_HAL_IO_V4

#ifdef MVBPROJ_HAL_IO_V7A

#define GPIO_CONTROL_GROUP_IDR	GPIO_C_IDR
#define GPIO_CONTROL_GROUP_ODR	GPIO_C_ODR
#define GPIO_DATA_GROUP_IDR		GPIO_A_IDR
#define GPIO_DATA_GROUP_ODR		GPIO_A_ODR

#endif // ifdef MVBPROJ_HAL_IO_V7A

#ifdef MVBPROJ_HAL_IO_V8

#define GPIO_CONTROL_GROUP_IDR	GPIO_C_IDR
#define GPIO_CONTROL_GROUP_ODR	GPIO_C_ODR
#define GPIO_DATA_GROUP_IDR		GPIO_A_IDR
#define GPIO_DATA_GROUP_ODR		GPIO_A_ODR

#endif // ifdef MVBPROJ_HAL_IO_V8

//=============================================================================
// AIO Group 1 : GPIO_CONTROL_GROUP
//
// + Note:
//
//   - Version 1
//   PA[0]      sync read flag        aio[10]
//   PA[1]		init finish flag      aio[11]
//   PA[2]		init write flag       aio[12]
//   PA[3]		sync write flag       aio[13]
//   PA[12]		main/slave frame flag aio[8]
//   PA[13]		frame send flag       aio[9]
//   PA[14]		frame read flag       aio[14]
//   PA[15]		frame write flag      aio[15]
//
//   - Version 4
//   PC[15]		frame write flag      aio[15]
//   PC[0]		frame read flag       aio[14] * DEPRECATED *
//   PC[7]		sync write flag       aio[13]
//   PC[8]		init write flag       aio[12]
//   PC[9]		init finish flag      aio[11]
//   PC[12]		sync read flag        aio[10]
//   PC[13]		frame send flag       aio[9]
//   PC[14]		main/slave frame flag aio[8]
//
//   - Version 7a
//   PC[15]		frame write flag      aio[15]
//   PC[0]		frame read flag       aio[14]
//   PC[7]		sync write flag       aio[13]
//   PC[8]		init write flag       aio[12]
//   PC[9]		init finish flag      aio[11]
//   PC[12]		sync read flag        aio[10]
//   PC[13]		frame send flag       aio[9]
//   PC[14]		main/slave frame flag aio[8]
//
//   - Version 8
//   PC[0]		init write flag       C10
//   PC[1]		init finish flag      B10
//   PC[6]		main/slave frame flag C1
//   PC[7]		frame read flag       C2
//   PC[8]		frame write flag      B2
//   PC[9]		frame send flag       C3
//   PC[12]		sync read flag        A5
//   PC[13]		sync write flag       A8
//
#ifdef MVBPROJ_HAL_IO_V1

#define GPIO_AIO_FRAME_WRITE_FLAG	0x00008000
#define GPIO_AIO_FRAME_READ_FLAG	0x00004000
#define GPIO_AIO_FRAME_SEND_FLAG	0x00002000
#define GPIO_AIO_FRAME_FLAG			0x00001000

#define GPIO_AIO_SYNC_WRITE_FLAG	0x00000008
#define GPIO_AIO_INIT_WRITE_FLAG	0x00000004
#define GPIO_AIO_INIT_FINISH_FLAG	0x00000002
#define GPIO_AIO_SYNC_READ_FLAG		0x00000001

#endif // ifdef MVBPROJ_HAL_IO_V1

#ifdef MVBPROJ_HAL_IO_V4

#define GPIO_AIO_FRAME_WRITE_FLAG	0x00008000
#define GPIO_AIO_FRAME_READ_FLAG	0x00000001
#define GPIO_AIO_FRAME_SEND_FLAG	0x00002000
#define GPIO_AIO_FRAME_FLAG			0x00004000

#define GPIO_AIO_SYNC_WRITE_FLAG	0x00000080
#define GPIO_AIO_INIT_WRITE_FLAG	0x00000100
#define GPIO_AIO_INIT_FINISH_FLAG	0x00000200
#define GPIO_AIO_SYNC_READ_FLAG		0x00001000

#endif // ifdef MVBPROJ_HAL_IO_V4

#ifdef MVBPROJ_HAL_IO_V7A

#define GPIO_AIO_FRAME_WRITE_FLAG	0x00008000
#define GPIO_AIO_FRAME_READ_FLAG	0x00000001
#define GPIO_AIO_FRAME_SEND_FLAG	0x00002000
#define GPIO_AIO_FRAME_FLAG			0x00004000

#define GPIO_AIO_SYNC_WRITE_FLAG	0x00000080
#define GPIO_AIO_INIT_WRITE_FLAG	0x00000100
#define GPIO_AIO_INIT_FINISH_FLAG	0x00000200
#define GPIO_AIO_SYNC_READ_FLAG		0x00001000

#endif // ifdef MVBPROJ_HAL_IO_V7A

#ifdef MVBPROJ_HAL_IO_V8

#define GPIO_AIO_INIT_WRITE_FLAG	0x00000001
#define GPIO_AIO_INIT_FINISH_FLAG	0x00000002

#define GPIO_AIO_FRAME_FLAG			0x00000040
#define GPIO_AIO_FRAME_READ_FLAG	0x00000080
#define GPIO_AIO_FRAME_WRITE_FLAG	0x00000100
#define GPIO_AIO_FRAME_SEND_FLAG	0x00000200

#define GPIO_AIO_SYNC_READ_FLAG		0x00001000
#define GPIO_AIO_SYNC_WRITE_FLAG	0x00002000

#endif // ifdef MVBPROJ_HAL_IO_V8

//=============================================================================
// Macros for basic hardware abstraction layer calls
// Not recommended to be used directly

// This macro initialize GPIO pin group as floating input mode
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_init_all_gpio()
#define HAL_IO_INIT_GPIO_IN(__port) \
	for (_hal_io_loop_i = 0; _hal_io_loop_i < 16; _hal_io_loop_i++) \
	{ \
		cyg_uint32 pin; \
		pin = CYGHWR_HAL_STM32_PIN_IN(__port, _hal_io_loop_i, NONE); \
		CYGHWR_HAL_STM32_GPIO_SET(pin); \
	}

// This macro initialize GPIO pin group as pushpull output mode with fast speed and pullup
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_init_all_gpio()
#define HAL_IO_INIT_GPIO_OUT(__port) \
	for (_hal_io_loop_i = 0; _hal_io_loop_i < 16; _hal_io_loop_i++) \
	{ \
		cyg_uint32 pin; \
		pin = CYGHWR_HAL_STM32_PIN_OUT(__port, _hal_io_loop_i, PUSHPULL, NONE, LOW); \
		CYGHWR_HAL_STM32_GPIO_SET(pin); \
	}

// Macro for AIO sending initialize finish signal (pulse)
#define HAL_IO_INIT_FINISH \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, GPIO_AIO_INIT_FINISH_FLAG); \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, IO_RESET);

// Macro for AIO sending initialize write signal (pulse)
#define HAL_IO_INIT_OUTPUT_PULSE \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, GPIO_AIO_INIT_WRITE_FLAG); \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, IO_RESET);

// Macro for AIO sending synchronization read signal
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_receive_status(cyg_uint16 content)
#define HAL_IO_SYNC_READ_SIGNAL \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, GPIO_AIO_SYNC_READ_FLAG);

// Macro for AIO sending synchronization writing signal (pulse)
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_send_status(cyg_uint16 mvb_device_status_16)
#define	HAL_IO_SYNC_WRITE_SIGNAL_PULSE \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, GPIO_AIO_SYNC_WRITE_FLAG); \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, IO_RESET);

// This macro reads data from IDR register (data group)
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_receive_status(cyg_uint16 content)
//          mvb_arm_receive_frame(cyg_uint16 content)
//          mvb_arm_receive_frame_q(cyg_uint16 content)
#define	HAL_IO_INPUT(__data) \
	HAL_READ_UINT32(GPIO_DATA_GROUP_IDR, __data);

// This macro writes data to DIO ODR register (GPIO group B)
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_send_status(cyg_uint16 content)
//          mvb_arm_send_main_frame(cyg_uint16 content)
//          mvb_arm_send_main_frame_f(f_code, address)
//          mvb_arm_send_slave_frame(cyg_uint16 content)
#define HAL_IO_OUTPUT(__data) \
	HAL_WRITE_UINT32(GPIO_DATA_GROUP_ODR, __data);

// Macro for AIO sending reading signal
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_receive_frame(cyg_uint16 content)
//          mvb_arm_receive_frame_q(cyg_uint16 content)
#define	HAL_IO_FRAME_READ_SIGNAL \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, GPIO_AIO_FRAME_READ_FLAG);

// Macro for AIO sending reading signal (pulse)
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_receive_frame(cyg_uint16 content)
//          mvb_arm_receive_frame_q(cyg_uint16 content)
#define	HAL_IO_FRAME_READ_SIGNAL_PULSE \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, GPIO_AIO_FRAME_READ_FLAG); \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, IO_RESET);

// Macro for AIO sending writing signal with address (pulse)
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_send_main_frame(cyg_uint16 content)
//          mvb_arm_send_main_frame_f(f_code, address)
//          mvb_arm_send_slave_frame(cyg_uint16 content)
#define	HAL_IO_FRAME_WRITE_SIGNAL_PULSE \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, GPIO_AIO_FRAME_WRITE_FLAG); \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, IO_RESET);

// Macro for AIO sending main frame flag with send action signal (pulse)
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_send_main_frame(cyg_uint16 content)
//          mvb_arm_send_main_frame_f(f_code, address)
#define	HAL_IO_SEND_MAIN_FRAME \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, GPIO_AIO_FRAME_FLAG);\
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, GPIO_AIO_FRAME_SEND_FLAG | GPIO_AIO_FRAME_FLAG ); \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, IO_RESET);

// Macro for AIO sending slave frame flag with send action signal (pulse)
// Caution: DO NOT use this macro directly. Instead:
//          mvb_arm_send_slave_frame(cyg_uint16 content)
#define	HAL_IO_SEND_SLAVE_FRAME \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, GPIO_AIO_FRAME_SEND_FLAG); \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, IO_RESET);

//=============================================================================
// RCC/SYSCFG register address
#define RCC_BASE		0x40023800
#define SYSCFG_BASE		0x40013800

#define RCC_APB2ENR		(RCC_BASE + 0x044)
#define SYSCFG_EXTICR1	(SYSCFG_BASE + 0x008)
#define SYSCFG_EXTICR2	(SYSCFG_BASE + 0x00C)
#define SYSCFG_EXTICR3	(SYSCFG_BASE + 0x010)
#define SYSCFG_EXTICR4	(SYSCFG_BASE + 0x014)

//=============================================================================
// AIO Group 2 : GPIO_INTERRUPT_GROUP
// + Note:
//
//   - Version 1
//   PH[8]		uart interrupt                  aio[0]
//   PH[9]		supervisory phase interrupt     aio[1]
//   PH[10]		timeout interrupt               aio[2]
//   PH[11]		error frame interrupt           aio[3]
//   PH[12]		valid frame received interrupt  aio[4]
//   PH[7]		sync status interrupt           aio[5]
//   PH[14]		no time interrupt               aio[6]
//   PH[15]		frame status flag               aio[7]
//
//   - Version 4
//   PE[2]		supervisory phase interrupt   * aio[1]
//   PH[8]		timeout interrupt             * aio[2] // origin: PB[8]
//   PH[7]		error frame interrupt           aio[3] // origin: PB[7]
//   PE[6]		valid frame interrupt           aio[4] // origin: PB[6]  * DEPRECATED *
//   PE[6]		main frame interrupt            aio[4]
//   PH[4]		slave frame interrupt           aio[14]
//   PH[3]		sync interrupt                  aio[5] // origin: PE[0]
//   PH[5]		no time interrupt             * aio[6] // origin: PB[5]
//   PB[9]		frame status flag               aio[7]
//   PH[2]		sync flag						aio[?]
//   PH[15]		uart flag                     * aio[0]
//
//   - Version 7a
//   PF[6]		main frame interrupt            aio[4]	C11
//   PF[7]		slave frame interrupt           aio[14]	A12
//   PG[11]		supervisory phase interrupt     aio[1]	F5
//   PG[12]		sync interrupt                  aio[5]	C5
//   PG[13]		no time interrupt               aio[6]	A4
//   PG[14]		timeout interrupt               aio[2]	B5
//   PG[15]		error frame interrupt           aio[3]	A5
//   PB[5]		frame status flag               aio[7]	D5
//   PB[6]		sync flag                       aio[?]	G6
//   PB[7]		uart flag                       aio[0]	B6
//
//   - Version 8
//   PG[7]		main frame interrupt            D1
//   PG[8]		slave frame interrupt			B1
//   PG[10]		supervisory phase interrupt		C5
//   PG[11]		sync interrupt					B6
//   PG[12]		no time interrupt				A6
//   PG[13]		timeout interrupt				C6
//   PG[15]		error frame interrupt			A7
//   PF[6]		frame status flag				A9
//   PF[7]		sync flag						C9
//   PF[10]		uart flag						A10


#ifdef MVBPROJ_HAL_IO_V1

#define EXTI_FRAME_STATUS					0x00008000
#define EXTI_NO_TIME						0x00004000
#define EXTI_SYNC_STATUS					0x00000080 // special PH[7]
#define EXTI_VALID_FRAME					0x00001000
#define EXTI_ERROR_FRAME					0x00000800
#define EXTI_TIMEOUT						0x00000400
#define EXTI_SUPERVISORY_INT				0x00000200
#define EXTI_UART_INT						0x00000100

#define	EXTI_NO_TIME_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI14
#define	EXTI_SYNC_STATUS_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI7 // special PH[7] => EXTI7
#define	EXTI_VALID_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI12
#define	EXTI_ERROR_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI11
#define	EXTI_TIMEOUT_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI10
#define	EXTI_SUPERVISORY_INT_VECTOR			CYGNUM_HAL_INTERRUPT_EXTI9
#define	EXTI_UART_INT_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI8

#endif // ifdef MVBPROJ_HAL_IO_V1

#ifdef MVBPROJ_HAL_IO_V4

#define EXTI_FRAME_STATUS					0x00000200
#define EXTI_NO_TIME						0x00000020
#define EXTI_SYNC							0x00000008
#define EXTI_VALID_FRAME					0x00000040  // * DEPRECATED *
#define EXTI_MAIN_FRAME						0x00000040
#define EXTI_SLAVE_FRAME					0x00000200
#define EXTI_ERROR_FRAME					0x00000080
#define EXTI_TIMEOUT						0x00000100
#define EXTI_SUPERVISORY_INT				0x00000004

#define	EXTI_NO_TIME_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI5
#define	EXTI_SYNC_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI3
#define	EXTI_VALID_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI6 // * DEPRECATED *
#define	EXTI_MAIN_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI6
#define	EXTI_SLAVE_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI4
#define	EXTI_ERROR_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI7
#define	EXTI_TIMEOUT_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI8
#define	EXTI_SUPERVISORY_INT_VECTOR			CYGNUM_HAL_INTERRUPT_EXTI2

#endif // ifdef MVBPROJ_HAL_IO_V4

#ifdef MVBPROJ_HAL_IO_V7A

#define EXTI_MAIN_FRAME						0x00000040
#define EXTI_SLAVE_FRAME					0x00000080
#define EXTI_SUPERVISORY_INT				0x00000800
#define EXTI_SYNC							0x00001000
#define EXTI_NO_TIME						0x00002000
#define EXTI_TIMEOUT						0x00004000
#define EXTI_ERROR_FRAME					0x00008000

#define	EXTI_MAIN_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI6
#define	EXTI_SLAVE_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI7
#define	EXTI_SUPERVISORY_INT_VECTOR			CYGNUM_HAL_INTERRUPT_EXTI11
#define	EXTI_SYNC_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI12
#define	EXTI_NO_TIME_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI13
#define	EXTI_TIMEOUT_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI14
#define	EXTI_ERROR_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI15

#endif // ifdef MVBPROJ_HAL_IO_V7A

#ifdef MVBPROJ_HAL_IO_V8

#define EXTI_MAIN_FRAME						0x00000080
#define EXTI_SLAVE_FRAME					0x00000100
#define EXTI_SUPERVISORY_INT				0x00000400
#define EXTI_SYNC							0x00000800
#define EXTI_NO_TIME						0x00001000
#define EXTI_TIMEOUT						0x00002000
#define EXTI_ERROR_FRAME					0x00004000

#define	EXTI_MAIN_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI7
#define	EXTI_SLAVE_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI8
#define	EXTI_SUPERVISORY_INT_VECTOR			CYGNUM_HAL_INTERRUPT_EXTI10
#define	EXTI_SYNC_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI11
#define	EXTI_NO_TIME_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI12
#define	EXTI_TIMEOUT_VECTOR					CYGNUM_HAL_INTERRUPT_EXTI13
#define	EXTI_ERROR_FRAME_VECTOR				CYGNUM_HAL_INTERRUPT_EXTI14

#endif // ifdef MVBPROJ_HAL_IO_V8

// Macro for ISR/DSR reading frame/sync/uart flag

#ifdef MVBPROJ_HAL_IO_V1
#define	HAL_IO_FRAME_STATUS_PIN				( CYGHWR_HAL_STM32_PIN_IN(H, 15, NONE) )
#endif // ifdef MVBPROJ_HAL_IO_V1

#ifdef MVBPROJ_HAL_IO_V4
#define HAL_IO_FRAME_STATUS_PIN				( CYGHWR_HAL_STM32_PIN_IN(B, 9, NONE) )
#define HAL_IO_SYNC_TYPE_PIN				( CYGHWR_HAL_STM32_PIN_IN(H, 2, NONE) )
#define HAL_IO_UART_STATUS_PIN				( CYGHWR_HAL_STM32_PIN_IN(H, 15, NONE) )
#endif // ifdef MVBPROJ_HAL_IO_V4

#ifdef MVBPROJ_HAL_IO_V7A
#define HAL_IO_FRAME_STATUS_PIN				( CYGHWR_HAL_STM32_PIN_IN(B, 5, NONE) )
#define HAL_IO_SYNC_TYPE_PIN				( CYGHWR_HAL_STM32_PIN_IN(B, 6, NONE) )
#define HAL_IO_UART_STATUS_PIN				( CYGHWR_HAL_STM32_PIN_IN(B, 7, NONE) )
#endif // ifdef MVBPROJ_HAL_IO_V7A

#ifdef MVBPROJ_HAL_IO_V8
#define HAL_IO_FRAME_STATUS_PIN				( CYGHWR_HAL_STM32_PIN_IN(F, 6, NONE) )
#define HAL_IO_SYNC_TYPE_PIN				( CYGHWR_HAL_STM32_PIN_IN(F, 7, NONE) )
#define HAL_IO_UART_STATUS_PIN				( CYGHWR_HAL_STM32_PIN_IN(F, 10, NONE) )
#endif // ifdef MVBPROJ_HAL_IO_V8

#define	HAL_IO_FRAME_CHECKBIT(__val)		CYGHWR_HAL_STM32_GPIO_IN(HAL_IO_FRAME_STATUS_PIN, __val);
#define	HAL_IO_SYNC_CHECKBIT(__val)			CYGHWR_HAL_STM32_GPIO_IN(HAL_IO_SYNC_TYPE_PIN, __val);
#define	HAL_IO_UART_CHECKBIT(__val)			CYGHWR_HAL_STM32_GPIO_IN(HAL_IO_UART_STATUS_PIN, __val);

#define HAL_IO_ENUM_MAIN_FRAME		1
#define HAL_IO_ENUM_SLAVE_FRAME		0

#define HAL_IO_ENUM_SYNC_STATUS		0
#define HAL_IO_ENUM_SYNC_ADDRESS	1

#define HAL_IO_ENUM_UART_NOT_EMPTY	1
#define HAL_IO_ENUM_UART_EMPTY		0

//0-4 1-3 2
#define EXTI_NO_TIME_PRI				3
#define EXTI_SYNC_PRI					2
#define EXTI_VALID_FRAME_PRI			0 // * DEPRECATED *
#define EXTI_MAIN_FRAME_PRI				0
#define EXTI_SLAVE_FRAME_PRI			0
#define EXTI_ERROR_FRAME_PRI			4
#define EXTI_TIMEOUT_PRI				4
#define EXTI_SUPERVISORY_INT_PRI		1

//=============================================================================
// FPGA support
//
#define CYGNUM_FS_ROM_BASE_ADDRESS 0x08020000

#if !defined(MVBPROJ_HAL_IO_V8)

#define	HAL_IO_FPGA_CCLK		( CYGHWR_HAL_STM32_PIN_OUT( B , 1 , PUSHPULL , NONE , FAST ) )
#define HAL_IO_FPGA_INIT_B		( CYGHWR_HAL_STM32_PIN_IN(  B , 14 , NONE ) )
#define HAL_IO_FPGA_PROG_B		( CYGHWR_HAL_STM32_PIN_OUT( B , 15 , PUSHPULL , NONE , FAST ) )
#define HAL_IO_FPGA_PROG_DON	( CYGHWR_HAL_STM32_PIN_IN(  C , 4 , NONE ) )
#define HAL_IO_FPGA_DIN			( CYGHWR_HAL_STM32_PIN_OUT( E , 5 , PUSHPULL , NONE , FAST) )

#else

#define	HAL_IO_FPGA_CCLK		( CYGHWR_HAL_STM32_PIN_OUT( B , 8 , PUSHPULL , NONE , FAST ) )
#define HAL_IO_FPGA_INIT_B		( CYGHWR_HAL_STM32_PIN_IN(  B , 5 , NONE ) )
#define HAL_IO_FPGA_PROG_B		( CYGHWR_HAL_STM32_PIN_OUT( B , 6 , PUSHPULL , NONE , FAST ) )
#define HAL_IO_FPGA_PROG_DON	( CYGHWR_HAL_STM32_PIN_IN(  B , 9 , NONE ) )
#define HAL_IO_FPGA_DIN			( CYGHWR_HAL_STM32_PIN_OUT( B , 7 , PUSHPULL , NONE , FAST) )

#endif // if !defined(MVBPROJ_HAL_IO_V8)



cyg_uint16 _hal_io_loop_i;
cyg_uint32 _hal_io_temp32;

//=============================================================================
// LED support
//
// Function: mvb_arm_init_led(cyg_uint32 flag)
//           Initialize all LED pins and set the led status to flag
//
// Function: mvb_arm_active_led(cyg_uint32 flag)
//           Set the active led status to flag (supported by V4 above)
//
// Function: mvb_arm_master_led(cyg_uint32 flag)
//           Set the master led status to flag (supported by V4 above)
//
#ifdef MVBPROJ_LED_SUPPORT
#ifdef MVBPROJ_HAL_IO_V1
#define mvb_arm_init_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED1); \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED2); \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED3); \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED4); \
	\
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED1, __flag); \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED2, __flag); \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED3, __flag); \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED4, __flag);
#endif // ifdef MVBPROJ_HAL_IO_V1

#ifdef MVBPROJ_HAL_IO_V4
#define mvb_arm_init_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED1); \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED2); \
	\
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED1, __flag); \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED2, __flag);

#define mvb_arm_active_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED_ACTIVE, __flag);

#define mvb_arm_master_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED_MASTER, __flag);

#endif // ifdef MVBPROJ_HAL_IO_V4

#ifdef MVBPROJ_HAL_IO_V7A
#define mvb_arm_init_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED1); \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED2); \
	\
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED1, __flag); \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED2, __flag);

#define mvb_arm_active_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED_ACTIVE, __flag);

#define mvb_arm_master_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED_MASTER, __flag);

#endif // ifdef MVBPROJ_HAL_IO_V7A

#ifdef MVBPROJ_HAL_IO_V8
#define mvb_arm_init_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED1); \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED2); \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED3); \
	CYGHWR_HAL_STM32_GPIO_SET(MVB_ARM_LED4); \
	\
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED1, __flag); \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED2, __flag); \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED3, __flag); \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED4, __flag);

#define mvb_arm_active_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED_ACTIVE, __flag);

#define mvb_arm_master_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED_MASTER, __flag);

#define mvb_arm_line_a_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED_LINE_A, __flag);

#define mvb_arm_line_b_led(__flag) \
	CYGHWR_HAL_STM32_GPIO_OUT(MVB_ARM_LED_LINE_B, __flag);

#endif // ifdef MVBPROJ_HAL_IO_V8

#endif // ifdef MVBPROJ_LED_SUPPORT

//=============================================================================
// GPIO initialization
//
// Function: mvb_arm_init_all_gpio()
//           Initialize all GPIO pins,
//           - Version 1
//           group H as floating input mode,
//           group A and B as pushpull output mode, fast speed and pullup
//           - Version 4
//           group B and E as floating input mode,
//           group A and C as pushpull output mode, fast speed and pullup

#ifdef MVBPROJ_HAL_IO_V1

#define mvb_arm_init_all_gpio() \
	HAL_IO_INIT_GPIO_OUT(A); \
	HAL_IO_INIT_GPIO_OUT(B); \
	HAL_IO_INIT_GPIO_IN(H);

#endif // ifdef MVBPROJ_HAL_IO_V1

#ifdef MVBPROJ_HAL_IO_V4

//	HAL_IO_INIT_GPIO_OUT(C); HAL_IO_INIT_GPIO_OUT(A);
#define mvb_arm_init_all_gpio() \
	HAL_IO_INIT_GPIO_OUT(A); \
	cyg_uint32 pin; \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 0, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 7, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 8, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 9, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 12, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 13, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 14, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 15, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(B, 6, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(B, 9, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(E, 2, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(E, 6, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(H, 2, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(H, 3, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(H, 4, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(H, 5, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(H, 7, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(H, 8, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \

#endif // ifdef MVBPROJ_HAL_IO_V7A

#ifdef MVBPROJ_HAL_IO_V7A

#define mvb_arm_init_all_gpio() \
	HAL_IO_INIT_GPIO_OUT(A); \
	cyg_uint32 pin; \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 0, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 5, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 7, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 8, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 9, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 12, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 13, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 14, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 15, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(B, 5, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(B, 6, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(B, 7, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(F, 6, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(F, 7, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 11, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 12, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 13, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 14, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 15, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \

#endif // ifdef MVBPROJ_HAL_IO_V7A

#ifdef MVBPROJ_HAL_IO_V8

#define mvb_arm_init_all_gpio() \
	HAL_IO_INIT_GPIO_OUT(A); \
	cyg_uint32 pin; \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 0, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 1, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 6, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 7, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 8, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 9, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 12, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 13, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_OUT(C, 14, PUSHPULL, PULLUP, FAST); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(F, 6, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(F, 7, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(F, 10, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 7, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 8, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 10, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 11, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 12, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 13, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 14, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \
	pin = CYGHWR_HAL_STM32_PIN_IN(G, 15, NONE); \
	CYGHWR_HAL_STM32_GPIO_SET(pin); \

#endif // ifdef MVBPROJ_HAL_IO_V8

//=============================================================================
// EXTI initialization
//
// Function: void mvb_arm_init_exti()
//           Open RCC clock, connect EXTI to correct pins
//
#ifdef MVBPROJ_HAL_IO_V1

#define mvb_arm_init_exti() \
	HAL_WRITE_UINT32(RCC_APB2ENR, 0x00004000); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR1, 0x00007777); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR2, 0x00007777); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR3, 0x00007777); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR4, 0x00007777);

#endif // ifdef MVBPROJ_HAL_IO_V1

#ifdef MVBPROJ_HAL_IO_V4

#define mvb_arm_init_exti() \
	HAL_WRITE_UINT32(RCC_APB2ENR, 0x00004000); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR1, 0x00007400); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR2, 0x00007477); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR3, 0x00000007); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR4, 0x00000000);

#endif // ifdef MVBPROJ_HAL_IO_V4

#ifdef MVBPROJ_HAL_IO_V7A

#define mvb_arm_init_exti() \
	HAL_WRITE_UINT32(RCC_APB2ENR, 0x00004000); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR1, 0x00000000); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR2, 0x00005500); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR3, 0x00006000); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR4, 0x00006666);

#endif // ifdef MVBPROJ_HAL_IO_V7A

#ifdef MVBPROJ_HAL_IO_V8

#define mvb_arm_init_exti() \
	HAL_WRITE_UINT32(RCC_APB2ENR, 0x00004000); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR1, 0x00006666); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR2, 0x00006666); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR3, 0x00006666); \
	HAL_WRITE_UINT32(SYSCFG_EXTICR4, 0x00006666);

#endif // ifdef MVBPROJ_HAL_IO_V8

//=============================================================================
// Status Sending
//
// Function: void mvb_arm_send_status(cyg_uint16 content)
//           Send status to FPGA (sync)
// Example:  cyg_uint16 device_status_16;
//           mvb_arm_send_status(device_status_16);
#define mvb_arm_send_status(__content) \
	HAL_IO_OUTPUT(IO_RESET | __content); \
	HAL_IO_SYNC_WRITE_SIGNAL_PULSE;


//=============================================================================
// Sync data Receieving
//
// Function: void mvb_arm_receive_sync(cyg_uint content)
//           Receieve status or address from FPGA (sync)
// Example:  mvb_arm_receive_sync(device_status);
//
#define mvb_arm_receive_sync(__content) \
	HAL_IO_SYNC_READ_SIGNAL; \
	mvb_arm_delay(HAL_DELAY_COUNT); \
	HAL_IO_INPUT(__content); \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, IO_RESET);

//=============================================================================
// Main Frame Sending
//
// Function: void mvb_arm_send_main_frame(cyg_uint16 content)
//           Send main frame to FPGA
// Example:  cyg_uint16 main_content;
//           main_content = 0xAAAA;
//           mvb_arm_send_main_frame(main_content);
//
// Function: void mvb_arm_send_main_frame_f(cyg_uint16 f_code, cyg_uint16 address)
//           Send main frame to FPGA
// Example:  mvb_arm_send_main_frame_f(15, this_address);
//
#define mvb_arm_send_main_frame(__content) \
	ba_mf = __content; \
	HAL_IO_OUTPUT(IO_RESET | __content); \
	HAL_IO_FRAME_WRITE_SIGNAL_PULSE; \
	HAL_IO_SEND_MAIN_FRAME;

#define mvb_arm_send_main_frame_f(__f_code, __address) \
	mvb_arm_send_main_frame(((__f_code & 0x000F) << 12) | (__address & 0x0FFF));

//=============================================================================
// Slave Frame Sending
//
// Function: void mvb_arm_send_slave_frame(cyg_uint16 content)
//           Send slave frame to FPGA
// Example:  cyg_uint16 slave_content;
//           slave_content = 0xAAAA;
//           mvb_arm_send_slave_frame(slave_content);
//
#define mvb_arm_send_slave_frame(__content) \
	HAL_IO_OUTPUT(IO_RESET | __content); \
	HAL_IO_FRAME_WRITE_SIGNAL_PULSE; \
	HAL_IO_SEND_SLAVE_FRAME;


//=============================================================================
// Message Data Sending
//
// Function: void mvb_arm_send_message()
//           Send message data
// Example:  mvb_arm_send_message();
//
#define mvb_arm_send_message() \
	HAL_IO_SEND_SLAVE_FRAME;

//=============================================================================
// Frame Receieving
//
// Function: void mvb_arm_receive_frame(cyg_uint content)
//           Receieve frame from FPGA
// Example:  cyg_uin16 content;
//           mvb_arm_receive_frame(content);
//
// Function: void mvb_arm_receive_frame_q(cyg_uint content)
//           Receieve frame from FPGA
// Example:  cyg_uin16 content;
//           mvb_arm_receive_frame_q(content);
//
#define mvb_arm_receive_frame(__content) \
	HAL_IO_FRAME_READ_SIGNAL; \
	mvb_arm_delay(HAL_DELAY_COUNT); \
	HAL_IO_INPUT(__content); \
	HAL_WRITE_UINT32(GPIO_CONTROL_GROUP_ODR, IO_RESET);

//=============================================================================
// Idle cycles
//
// Function: mvb_arm_delay(cyg_uint16 count)
//           Empty idle cycles
// Example:  cyg_uin16 content;
//           mvb_arm_delay(count);
//
#define mvb_arm_delay(__count) \
	_hal_io_loop_i = __count; \
	for (; _hal_io_loop_i != 0; _hal_io_loop_i--);

//-----------------------------------------------------------------------------
// end of hal.h
#endif // ifndef MVBONCE_HAL_H