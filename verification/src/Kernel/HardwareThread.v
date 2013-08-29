Set Implicit Arguments.

(*Add LoadPath "../HAL".
Require Import environment.
*)
Require Import "../HAL/Environment".

Definition thread_entry := nat.

Definition ADDRESS := nat.

Definition CYGNUM_KERNEL_THREADS_STACK_CHECK_DATA_SIZE := 0.

Record HardwareThread := mkHT {
  stack_base : ADDRESS;
  stack_size : nat;

  stack_limit : ADDRESS;

  stack_ptr : ADDRESS;
  
  entry_point : thread_entry;

  entry_data : ADDRESS;

  savedRegs : HAL_SavedRegisters
}.

(*TODO: HardwareThread_cstr*)

Definition get_stack_base ht := ht.(stack_base) - CYGNUM_KERNEL_THREADS_STACK_CHECK_DATA_SIZE.

Definition set_stack_base ht sb := 
  mkHT sb ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(savedRegs).

Definition get_stack_size ht := ht.(stack_size) + 2 * CYGNUM_KERNEL_THREADS_STACK_CHECK_DATA_SIZE.

Definition set_stack_size ht ss :=
  mkHT ht.(stack_base) ss ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(savedRegs).

Definition get_stack_limit ht := ht.(stack_limit).

Definition set_stack_limit ht sl :=
  mkHT ht.(stack_base) ht.(stack_size) sl ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(savedRegs).

Definition get_stack_ptr ht := ht.(stack_ptr).

Definition set_stack_ptr ht sp :=
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) sp ht.(entry_point) 
       ht.(entry_data) ht.(savedRegs).

Definition get_entry_point ht := ht.(entry_point).

Definition set_entry_point ht ep := 
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ep 
       ht.(entry_data) ht.(savedRegs).

Definition get_entry_data ht := ht.(entry_data).

Definition set_entry_data ht ed := 
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ed ht.(savedRegs).

Definition get_savedRegs ht := ht.(savedRegs).

Definition set_savedRegs ht regs := 
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) regs.

(*TODO: init_context*)

(*TODO: switch_context*)

(*TODO: attach_stack*)

(*TODO: detach_stack*)

(*TODO: prepare_exception*)

(*TODO: thread_entry*)