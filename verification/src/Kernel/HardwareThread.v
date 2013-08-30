Set Implicit Arguments.

(*Add LoadPath "../HAL".
Require Import Environment.
*)
Require Import "../HAL/Constants".
Require Import "../HAL/Environment".
Require Import NPeano.

Definition thread_entry := nat.

Definition ADDRESS := nat.

Definition CYGNUM_KERNEL_THREADS_STACK_CHECK_DATA_SIZE := 0.

(*  We implement a thread stack based on list of nat. 
 *  stack_base would be the list. 
 *  stack_ptr would be the last element of the list.
 *  stack_size would be the length of the list.
 *  saved_context points to the first element of HAL_savedRegisters in the list.
 *)

Record HardwareThread := mkHT {
  stack_base : ADDRESS;
  stack_size : nat;

  stack_limit : ADDRESS;

  stack_ptr : ADDRESS;
  
  entry_point : thread_entry;

  entry_data : ADDRESS;

  (*It was a pointer in thread.inl, with value 0 indicating that it points some real context*)
  saved_context : option HAL_SavedRegisters 
}.

Definition get_stack_base ht := ht.(stack_base) - CYGNUM_KERNEL_THREADS_STACK_CHECK_DATA_SIZE.

Definition set_stack_base ht sb := 
  mkHT sb ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(saved_context).

Definition get_stack_size ht := ht.(stack_size) + 2 * CYGNUM_KERNEL_THREADS_STACK_CHECK_DATA_SIZE.

Definition set_stack_size ht ss :=
  mkHT ht.(stack_base) ss ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(saved_context).

Definition get_stack_limit ht := ht.(stack_limit).

Definition set_stack_limit ht sl :=
  mkHT ht.(stack_base) ht.(stack_size) sl ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(saved_context).

Definition get_stack_ptr ht := ht.(stack_ptr).

Definition set_stack_ptr ht sp :=
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) sp ht.(entry_point) 
       ht.(entry_data) ht.(saved_context).

Definition get_entry_point ht := ht.(entry_point).

Definition set_entry_point ht ep := 
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ep 
       ht.(entry_data) ht.(saved_context).

Definition get_entry_data ht := ht.(entry_data).

Definition set_entry_data ht ed := 
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ed ht.(saved_context).

Definition get_saved_context ht := ht.(saved_context).

Definition set_saved_context ht regs := 
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) regs.

(*We don't use pointer here so only unique_id will suffice*)
Definition init_context (ht : HardwareThread)(uid : nat) : HardwareThread.
Print "/".
set (__sp := ht.(stack_ptr) / 8 * 8).
set (__ep := __sp - 4).  
set (__sp' := (__sp - 4) / 16 * 16).
Admitted.

(*TODO: switch_context*)

Definition attach_stack ht s_base s_size :=
  match ht with
  |mkHT _ _ _ _ ep ed sc => mkHT s_base s_size s_base (s_base + s_size) ep ed sc
  end. 

Definition HardwareThread_cstr e_point e_data s_size s_base :=
  attach_stack (mkHT 0 0 0 0 e_point e_data None) s_base s_size.

(*TODO: detach_stack*)

(*TODO: prepare_exception*)

(*TODO: thread_entry*)