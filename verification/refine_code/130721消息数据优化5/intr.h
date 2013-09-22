#ifndef MVBONCE_INTR_H
#define MVBONCE_INTR_H
//=============================================================================
//
//      intr.h
//
//      Interrupt header
//
//=============================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   Yinlong Su
// Date:        2012-08-16
// Modified:	2012-10-22
// Description: Interrupt header
// Version:     1.0
// Usage:       #include "intr.h"
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

// Standup thread configuration
#define SA_STACK_SIZE			256
#define SA_WORKTHREAD_PRI	2

// Extern function
extern void supervisory_interrupt_handle();
extern void ba_context_process(UNSIGNED8 sf_f_code, UNSIGNED16 sf_content_16, UNSIGNED8 vector);
extern UNSIGNED8 build_list_of_devices_scan(UNSIGNED16 address, BITSET16 status, bool flag_remove);

void exti_thread(cyg_addrword_t data);
void standup_alarm(cyg_handle_t alarm, cyg_addrword_t data);
void standup_thread(cyg_addrword_t data);

// ISR & DSR definition
cyg_uint32 supervisory_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data);
void supervisory_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data);
cyg_uint32 timeout_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data);
void timeout_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data);
cyg_uint32 errorframe_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data);
void errorframe_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data);
cyg_uint32 mainframe_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data);
void mainframe_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data);
cyg_uint32 slaveframe_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data);
void slaveframe_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data);
cyg_uint32 sync_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data);
void sync_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data);
cyg_uint32 notime_interrupt_isr(cyg_vector_t vector, cyg_addrword_t data);
void notime_interrupt_dsr(cyg_vector_t vector, cyg_ucount32 count, cyg_addrword_t data);

// Process handle
void mfprocess_handle(cyg_vector_t vector);
void sfprocess_handle(cyg_vector_t vector);
void syncprocess_handle();

// Checker
#define STATUS_CHECK(__status) (__status & 0x0C3F)


#endif // ifndef MVBONCE_INTR_H
