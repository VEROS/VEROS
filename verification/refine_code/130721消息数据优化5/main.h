#ifndef MVBONCE_MAIN_H
#define MVBONCE_MAIN_H
//=============================================================================
//
//      main.h
//
//      Main header
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Yinlong Su
// Date:        2012-08-16
// Modified:	2012-10-22
// Description: Main header
// Version:     1.0
// Usage:       #include "main.h"
//
//####DESCRIPTIONEND####
//
//=============================================================================
#include "mvb_project.h"
#include "mvb_def.h"
#include "hal.h"
#include <cyg/kernel/kapi.h>
#include <pkgconf/system.h>
#include <stdio.h>

// Build definition
#define MVB_BUILD_DEFINITION 1122

// Thread stack size
#define STACK_SIZE 256

// Thread priority
#define	START_WORKTHREAD_PRI	0
#define	EXTI_WORKTHREAD_PRI		1
#define LED_WORKTHREAD_PRI		3

// Thread function
extern void exti_thread(cyg_addrword_t data);
void start_thread(cyg_addrword_t data);
#ifdef MVBPROJ_LED_SUPPORT
void led_thread(cyg_addrword_t data);
#endif // ifdef MVBPROJ_LED_SUPPORT


void cyg_start(void);


// LED Setting
#define LED_FREQUENCY 5000

#endif // ifndef MVBONCE_MAIN_H
