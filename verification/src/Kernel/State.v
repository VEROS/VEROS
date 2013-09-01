Set Implicit Arguments.

Add LoadPath "../HAL".

Require Import Environment.
Require Import Thread.
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

(*pop into some register, t specifies the stack and regIndex specifies the destined register*)
Definition pop (rs : HAL_SavedRegisters)(t : Thread)(regIndex : nat) : (HAL_SavedRegisters * Thread).
destruct (Thread.pop t) as [t' n].
exact (Environment.set_core rs regIndex n, t').
Defined.

Definition update_thread s t := 
  set_kernel s (Kernel.update_thread s.(kernel) t).

(* 
 * hal_thread_load_context takes one parameter, next->stack_ptr which 
 * of course, stores in r0
 *)
Definition thread_load_context (s : State)(t : Thread) : State.
(*Based on our stack implementation, sp means the index of last pushed element in the stack,
 *which is zero, since it's the head of the list always. sp is useless here.
 *)
set (s' := set_core_register s 13 0). 
set (p1 := pop (get_regs s') t 2).
set (p2 := pop (fst p1) (snd p1) 3).
set (p3 := pop (fst p2) (snd p2) 4).
set (rs := Environment.set_basepri (fst p3) (Environment.get_core (fst p3) 3)).

(*pop into r0-r12*)
set (p4 := pop rs (snd p3) 0).
set (p5 := pop (fst p4) (snd p4) 1).
set (p6 := pop (fst p5) (snd p5) 2).
set (p7 := pop (fst p6) (snd p6) 3).
set (p8 := pop (fst p7) (snd p7) 4).
set (p9 := pop (fst p8) (snd p8) 5).
set (p10 := pop (fst p9) (snd p9) 6).
set (p11 := pop (fst p10) (snd p10) 7).
set (p12 := pop (fst p11) (snd p11) 8).
set (p13 := pop (fst p12) (snd p12) 9).
set (p14 := pop (fst p13) (snd p13) 10).
set (p15 := pop (fst p14) (snd p14) 11).
set (p16 := pop (fst p15) (snd p15) 12).

set (p17 := pop (fst p16) (snd p16) 15). (*pop into pc*)

(*All the poping is done, now we need to update the state*)
exact (update_thread (set_regs s' (fst p17)) (snd p17)).
Defined.

Definition thread_switch_context (s : State) (to from : Thread) : State.
