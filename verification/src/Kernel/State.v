Set Implicit Arguments.

Add LoadPath "../HAL".

Require Import Environment.
Require Import Kernel.

Record State := mkState{
  regs : HAL_SavedRegisters;
  kernel : Kernel
}.

Definition get_regs s := s.(regs).

Definition set_regs s rs := mkState rs s.(kernel).

Definition get_kernel s := s.(kernel).

Definition set_kernel s k := mkState s.(regs) k.

Definition get_core_register s n := Environment.get_core s.(regs) n.

Definition set_core_register s n v := 
  mkState (Environment.set_core s.(regs) n v) s.(kernel).

Definition get_basepri s := Environment.get_basepri s.(regs).

Definition set_basepri s n := 
  mkState (Environment.set_basepri s.(regs) n) s.(kernel).

(* 
 * hal_thread_load_context takes one parameter, next->stack_ptr which 
 * of course, stores in r0
 *)
Definition thread_load_context (s : State)(t : Thread.Thread) : State.


Definition thread_switch_context (s : State) (t1 t2 : Thread) : State.
