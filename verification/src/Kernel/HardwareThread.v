Set Implicit Arguments.

Add LoadPath "../HAL".
Require Import Environment.
Require Import NPeano.

Definition thread_entry := nat.

Definition CYGNUM_KERNEL_THREADS_STACK_CHECK_DATA_SIZE := 0.

(*  We implement a thread stack based on list of nat. 
 *  stack_base points to the first element of the stack, which is useless here 
 *  stack_ptr points to the last element of the stack, which is zero all the time, so useless 
 *  stack_size would be the length of the list.
 *  saved_context is the HAL_SavedRegisters, which is in thread stack
 *  By "points to", I mean "be the index of"...
 *)

Record HardwareThread := mkHT {
  stack_base : nat;
  stack_size : nat;

  stack_limit : nat;

  stack_ptr : nat;
  
  entry_point : thread_entry; (*pointer to the function*)

  entry_data : nat; (*pointer to the data*)

  (* indicating the last element of "Hal_SavedRegister" *)
  saved_context : nat; 
  
  (* Thread stack, in reverse order, that is, the last pushed element is the head *)
  stack : list nat
}.

Definition get_stack_base ht := ht.(stack_base) - CYGNUM_KERNEL_THREADS_STACK_CHECK_DATA_SIZE.

Definition set_stack_base ht sb := 
  mkHT sb ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(saved_context) ht.(stack).

Definition get_stack_size ht := ht.(stack_size) + 2 * CYGNUM_KERNEL_THREADS_STACK_CHECK_DATA_SIZE.

Definition set_stack_size ht ss :=
  mkHT ht.(stack_base) ss ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(saved_context) ht.(stack).

Definition get_stack_limit ht := ht.(stack_limit).

Definition set_stack_limit ht sl :=
  mkHT ht.(stack_base) ht.(stack_size) sl ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(saved_context) ht.(stack).

Definition get_stack_ptr ht := ht.(stack_ptr).

Definition set_stack_ptr ht sp :=
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) sp ht.(entry_point) 
       ht.(entry_data) ht.(saved_context) ht.(stack).

Definition get_entry_point ht := ht.(entry_point).

Definition set_entry_point ht ep := 
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ep 
       ht.(entry_data) ht.(saved_context) ht.(stack).

Definition get_entry_data ht := ht.(entry_data).

Definition set_entry_data ht ed := 
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ed ht.(saved_context) ht.(stack).

Definition get_saved_context ht := ht.(saved_context).

Definition set_saved_context ht regs := 
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) regs ht.(stack).

Definition get_stack ht := ht.(stack).

Definition set_stack ht st :=  
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(saved_context) st.

Definition push ht n :=
  mkHT ht.(stack_base) ht.(stack_size) ht.(stack_limit) ht.(stack_ptr) ht.(entry_point) 
       ht.(entry_data) ht.(saved_context) (cons n ht.(stack)).

Definition pop (ht : HardwareThread) : HardwareThread * nat.
destruct ht.(stack) as [|n l].
- exact (ht, 0).
- exact (set_stack ht l, n).
Defined.
 
(*We don't use pointer here so only unique_id will suffice*)
Definition init_context ht uid : HardwareThread :=
  push (push (push (push (push (push (push (push (push (push (push (push (push (push 
    (push (push (push (push ht ht.(entry_point)(*pc*)) 0(*r12*)) ht.(entry_point)(*r11*)) 
       0(*r10*)) 0(*r9*)) 0(*r8*)) 0(*r7*)) 0(*r6*)) 0(*r5*)) 0(*r4*)) 0(*r3*)) 0(*r2*)) 
          0(*r2*)) 0(*r1, should be 0x11110000*)) uid(*should be thread pointer*)) 0(*sp*)) 
             0(*basepri*)) 2(*type*).  

(*Defined in State.v : switch_context *)

Definition attach_stack ht s_base s_size :=
  match ht with
  |mkHT _ _ _ _ ep ed sc st => mkHT s_base s_size s_base (s_base + s_size) ep ed sc st
  end. 

Definition HardwareThread_cstr e_point e_data s_size s_base :=
  attach_stack (mkHT 0 0 0 0 e_point e_data 0 nil) 
               s_base s_size.

(*TODO: detach_stack, no definition found*)

(*TODO: prepare_exception*)

(*TODO: thread_entry*)