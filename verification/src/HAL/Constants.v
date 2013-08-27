(**
This file defines all the constants for VEROS
Author: Shengpeng Liu 
Date: May 24, 2013
*)


Definition CYGNUM_HAL_ISR_COUNT := 32.
Definition CYGNUM_HAL_VSR_COUNT := 8.

Section VectorNumber.
  (*Exceptions*)
  Definition CYGNUM_HAL_VECTOR_STACK := 0. (*Reset stack pointer*)
  Definition CYGNUM_HAL_VECTOR_RESET := 1. (*Reset entry point*)
  Definition CYGNUM_HAL_VECTOR_NMI := 2. (*Non-Maskable Interrupt*)
  Definition CYGNUM_HAL_VECTOR_HARD_FAULT := 3. (*Hard fault*)
  Definition CYGNUM_HAL_VECTOR_MEMORY_MAN := 4. (*Memory management (M3)*)
  Definition CYGNUM_HAL_VECTOR_BUS_FAULT := 5. (*Bus Fault*)
  Definition CYGNUM_HAL_VECTOR_USAGE_FAULT := 6. (*Usage Fault*)
  Definition CYGNUM_HAL_VECTOR_RESERVED_07 := 7.
  Definition CYGNUM_HAL_VECTOR_RESERVED_08 := 8. 
  Definition CYGNUM_HAL_VECTOR_RESERVED_09 := 9. 
  Definition CYGNUM_HAL_VECTOR_RESERVED_10 := 10.
  Definition CYGNUM_HAL_VECTOR_SERVICE := 11. (*System service call*)
  Definition CYGNUM_HAL_VECTOR_DEBUG := 12. (*Debug monitor (M3)*)
  Definition CYGNUM_HAL_VECTOR_RESERVED_13 := 13. 
  Definition CYGNUM_HAL_VECTOR_PENDSV := 14. (*Pendable svc request*)
  Definition CYGNUM_HAL_VECTOR_SYS_TICK := 15. (*System timer tick*)
  Definition CYGNUM_HAL_VECTOR_EXTERNAL := 16. (*Base of external interrupts*)

  (*Interrupts*)
  Definition CYGNUM_HAL_INTERRUPT_SYS_TICK := 0.
  Definition CYGNUM_HAL_INTERRUPT_EXTERNAL := 1.

  (*Aliases*)
  Definition CYGNUM_HAL_EXCEPTION_DATA_TLBMISS_ACCESS := CYGNUM_HAL_VECTOR_MEMORY_MAN.
  Definition CYGNUM_HAL_EXCEPTION_CODE_TLBMISS_ACCESS := CYGNUM_HAL_VECTOR_MEMORY_MAN.
  Definition CYGNUM_HAL_EXCEPTION_DATA_ACCESS := CYGNUM_HAL_VECTOR_BUS_FAULT.
  Definition CYGNUM_HAL_EXCEPTION_CODE_ACCESS := CYGNUM_HAL_VECTOR_BUS_FAULT.
  Definition CYGNUM_HAL_EXCEPTION_ILLEGAL_INSTRUCTION := CYGNUM_HAL_VECTOR_USAGE_FAULT.
  Definition CYGNUM_HAL_EXCEPTION_DATA_UNALIGNED_ACCESS := CYGNUM_HAL_VECTOR_USAGE_FAULT.
  Definition CYGNUM_HAL_EXCEPTION_INTERRUPT := CYGNUM_HAL_VECTOR_SERVICE.

  (*Some constants*)
  Definition CYGNUM_HAL_EXCEPTION_MIN := CYGNUM_HAL_EXCEPTION_DATA_UNALIGNED_ACCESS. 
  Definition CYGNUM_HAL_EXCEPTION_MAX := CYGNUM_HAL_EXCEPTION_INTERRUPT.
  Definition CYGNUM_HAL_EXCEPTION_COUNT := CYGNUM_HAL_EXCEPTION_MAX - 1.
  Definition CYGNUM_HAL_EXCEPTION_COUNT_1 := CYGNUM_HAL_EXCEPTION_MIN + 1. (*Need to check with Guo*)

End VectorNumber.