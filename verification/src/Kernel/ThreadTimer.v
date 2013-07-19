Set Implicit Arguments.

Require Import EqNat.
Require Import DLClist.
Require Import Alarm.

Record ThreadTimer := mkTT{
  alarm : Alarm;
  thread_id : nat
}.

Definition ThreadTimer_cstr aid cid thid :=
  mkTT (Alarm_cstr aid cid) thid.

(*TODO: ThreadTimer_enable, encapsulation of Alarm_enable*)

(*TODO: ThreadTimer_disable, encapsulation of Alarm_disable*)

Definition get_thread_timer_id tt := tt.(alarm).(alarm_id).

Definition get_thread_id tt := tt.(thread_id).

Definition get_thread_times tt := get_times tt.(alarm).

(*TODO: ThreadTimer_initialize, encapsulation of Alarm_initialize*)

(*TODO: ThreadTimer_alarm*)

(****************************************************************)
(*The list of thread timers, which will be in a clock*)

Module ThreadTimer_obj <: DNode.

  Definition Obj := ThreadTimer.

  Definition eq_Obj (x y : ThreadTimer) :=
    beq_nat x.(alarm).(alarm_id) y.(alarm).(alarm_id).

End ThreadTimer_obj.

(*The cycled double linked list of alarm*)
Module TTL := CList ThreadTimer_obj.

Definition ThreadTimerList := TTL.CList ThreadTimer.