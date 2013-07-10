Set Implicit Arguments.

Require Import EqNat.
Require Import DLClist.
Require Import Alarm.

Record ThreadTimer := mkTT{
  
  alarm : Alarm;
  thread_id : nat

}.

Definition Thread_Timer_cstr (r : ThreadTimer) (th : nat) :=
  mkTT (alarm r) th.


(****************************************************************)
(*The list of thread timers, which will be in a clock*)

Module ThreadTimer_obj <: DNode.

  Definition Obj := ThreadTimer.

  Definition eq_Obj (x y : ThreadTimer) :=
    beq_nat x.(alarm).(unique_id) y.(alarm).(unique_id).

End ThreadTimer_obj.

(*The cycled double linked list of alarm*)
Module TTL := CList ThreadTimer_obj.

Definition ThreadTimerList := TTL.CList Alarm.