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

(*r0 1, just pop into r0; r1 2, pop into r1 and r2*)
Fixpoint pop_many (rs : HAL_SavedRegisters)(t : Thread)(regIndex range : nat) 
  : (HAL_SavedRegisters * Thread).
induction range as [|n].
-exact (rs, t).
-destruct (pop rs t regIndex) as [rs' t']. 
 exact (pop_many rs' t' (S regIndex) n).
Defined.

(*push some register, t specifies the stack and regIndex specifies the destined register*)
Definition push (rs : HAL_SavedRegisters)(t : Thread)(regIndex : nat) : Thread :=
  Thread.push t (Environment.get_core rs regIndex).

(*r0 1, just push r0; r1 2, push r2, and then push r1, attention to the order*)
Fixpoint push_many (rs : HAL_SavedRegisters)(t : Thread)(regIndex range : nat) : Thread.
induction range as [|n].
-exact t.
-exact (push_many rs (push rs t (regIndex + n)) regIndex n).
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
set (p1 := pop_many (get_regs s') t 2 3).
set (rs := Environment.set_basepri (fst p1) (Environment.get_core (fst p1) 3)).

(*pop into r0-r12*)
set (p2 := pop_many rs (snd p1) 0 13).
set (p3 := pop (fst p2) (snd p2) 15). (*pop into pc*)

(*All the poping is done, now we need to update the state*)
exact (update_thread (set_regs s' (fst p3)) (snd p3)).
Defined.

Definition thread_switch_context (s : State) (to from : Thread) : State.
set (rs := get_regs s).
set (t1 := push rs from 14). (*push lr*)
set (t2 := push_many rs t1 0 13). (*push r0-r12, in reverse order*)
set (rs1 := Environment.set_core rs 2 2)  .
set (rs2 := Environment.set_core rs1 3 (Environment.get_basepri rs1)).
set (rs3 := Environment.set_core rs2 4 (Environment.get_core rs2 13)).
set (t3 := push_many rs3 t2 2 3).
set (t4 := Thread.set_stack_ptr t3 (Environment.get_core rs3 13)).
set (s' := update_thread (set_regs s rs3) t4).
exact (thread_load_context s' to).
Defined.