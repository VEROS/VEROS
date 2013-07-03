#ifndef CYGONCE_KERNEL_SMP_HXX
#define CYGONCE_KERNEL_SMP_HXX

//==========================================================================
//
//      smp.hxx
//
//      SMP kernel support
//
//==========================================================================
// ####ECOSGPLCOPYRIGHTBEGIN####                                            
// -------------------------------------------                              
// This file is part of eCos, the Embedded Configurable Operating System.   
// Copyright (C) 1998, 1999, 2000, 2001, 2002 Free Software Foundation, Inc.
//
// eCos is free software; you can redistribute it and/or modify it under    
// the terms of the GNU General Public License as published by the Free     
// Software Foundation; either version 2 or (at your option) any later      
// version.                                                                 
//
// eCos is distributed in the hope that it will be useful, but WITHOUT      
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or    
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License    
// for more details.                                                        
//
// You should have received a copy of the GNU General Public License        
// along with eCos; if not, write to the Free Software Foundation, Inc.,    
// 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.            
//
// As a special exception, if other files instantiate templates or use      
// macros or inline functions from this file, or you compile this file      
// and link it with other works to produce a work based on this file,       
// this file does not by itself cause the resulting work to be covered by   
// the GNU General Public License. However the source code for this file    
// must still be made available in accordance with section (3) of the GNU   
// General Public License v2.                                               
//
// This exception does not invalidate any other reasons why a work based    
// on this file might be covered by the GNU General Public License.         
// -------------------------------------------                              
// ####ECOSGPLCOPYRIGHTEND####                                              
//==========================================================================
//#####DESCRIPTIONBEGIN####
//
// Author(s):   nickg
// Contributors:nickg
// Date:        2001-02-10
// Purpose:     Kernel SMP support
// Description: If SMP support is configured into the kernel, then this file
//              translates HAL defined macros into C and C++ classes and methods
//              that can be called from the rest of the kernel. If SMP is not
//              configured in, then the same classes and methods are defined here
//              to operate correctly in a single CPU configuration.
//              
// Usage:       #include <cyg/kernel/smp.hxx>
//
//####DESCRIPTIONEND####
//
//==========================================================================

#include <cyg/kernel/ktypes.h>
#include <cyg/infra/cyg_ass.h>          // assertion macros

#include <cyg/hal/hal_intr.h>           // HAL_DISABLE_INTERRUPTS() etc.

#include <cyg/kernel/instrmnt.h>

//==========================================================================

//==========================================================================
// SMP support is NOT included.

#undef CYG_KERNEL_SMP_ENABLED

// -------------------------------------------------------------------------
// Defined values
// Supply a set of values that describe a single CPU system.

#ifndef HAL_SMP_CPU_TYPE
#define HAL_SMP_CPU_TYPE                cyg_uint32
#endif

#define CYGNUM_KERNEL_CPU_MAX           1

#define CYG_KERNEL_CPU_COUNT()          1

#define CYG_KERNEL_CPU_THIS()           0

#define CYG_KERNEL_CPU_NONE             -1

#define CYG_KERNEL_CPU_LOWPRI()         CYG_KERNEL_CPU_THIS()

// -------------------------------------------------------------------------
// SpinLock class
// This single CPU version simply goes through the motions of setting
// and clearing the lock variable for debugging purposes. 

//#ifdef __cplusplus

class Cyg_SpinLock
{
    volatile cyg_uint32 lock;

public:

    // Constructor, initialize the lock to clear
    Cyg_SpinLock() { lock = 0; };

    ~Cyg_SpinLock()
    {
        CYG_ASSERT( lock == 0, "spinlock still claimed");
    };
    
    // Spin on the lock. In this case we just set it to 1 and proceed.
    void spin()
    {
        CYG_ASSERT( lock == 0, "spinlock already claimed!");
        lock = 1;
    };

    // Clear the lock. Again, just set the value.
    void clear()
    {
        CYG_ASSERT( lock != 0, "spinlock already cleared!");
        lock = 0;
    };

    // Try to claim the lock. Return true if successful, false if not.
    cyg_bool trylock()
    {
        if( lock ) return false;
        else { lock = 1; return true; }
    };

    // Test the current value of the lock
    cyg_bool test() { return lock; };


    // The following two member functions are only necessary if the
    // spinlock is to be used in an ISR. 
    
    // Claim the spinlock, but also mask this CPU's interrupts while
    // we have it.
    void spin_intsave(CYG_INTERRUPT_STATE *state)
    {
        CYG_INTERRUPT_STATE s;
        HAL_DISABLE_INTERRUPTS(s);
        *state = s;
        spin();
    };

    // Clear the lock, and restore the interrupt state saved in
    // spin_intsave().
    void clear_intsave(CYG_INTERRUPT_STATE state)
    {
        clear();
        HAL_RESTORE_INTERRUPTS(state);
    };

};

// -------------------------------------------------------------------------
// Scheduler lock class

class Cyg_Scheduler_SchedLock
{
    static volatile cyg_ucount32 sched_lock         // lock counter
                    CYGBLD_ATTRIB_ASM_ALIAS( cyg_scheduler_sched_lock )
                    CYGBLD_ANNOTATE_VARIABLE_SCHED
                    ;
    
    // For non-SMP versions, the code here does the basic and obvious things.
protected:

    Cyg_Scheduler_SchedLock()
    {
        sched_lock = 1;
    };
    
    // Increment the scheduler lock, possibly taking it from zero to
    // one.
    static void inc_sched_lock()
    {
        sched_lock++;
    };

    static void zero_sched_lock()
    {
        CYG_ASSERT( sched_lock != 0, "Scheduler lock already zero");
        sched_lock = 0;
    };
    
    // Set the scheduler lock to a non-zero value. Both the scheduler
    // lock and the new value must be non-zero.
    static void set_sched_lock(cyg_uint32 new_lock)
    {
        CYG_ASSERT( new_lock > 0, "New scheduler lock value == 0");
        CYG_ASSERT( sched_lock > 0, "Scheduler lock == 0");
        sched_lock = new_lock;
    };

    static cyg_ucount32 get_sched_lock()
    {
        return sched_lock;
    };
};

#define CYGIMP_KERNEL_SCHED_LOCK_DEFINITIONS                    \
volatile cyg_ucount32 Cyg_Scheduler_SchedLock::sched_lock = 1;

//#endif // __cplusplus

#endif // defined(CYGSEM_KERNEL_SMP_SUPPORT) && (CYGSEM_HAL_SMP_SUPPORT)

// -------------------------------------------------------------------------
// ifndef CYGONCE_KERNEL_SMP_HXX

// EOF smp.hxx
