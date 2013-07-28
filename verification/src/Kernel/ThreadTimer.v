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

Definition get_timer_id tt := tt.(alarm).(alarm_id).

Definition get_thread_id tt := tt.(thread_id).

Definition get_thread_times tt := get_times tt.(alarm).

Definition get_interval tt := Alarm.get_interval tt.(alarm).

Definition get_trigger tt := Alarm.get_trigger tt.(alarm).

Definition get_enable tt := Alarm.get_enable tt.(alarm).

Definition set_alarm tt a := mkTT a tt.(thread_id). 

Definition set_enable tt b := set_alarm tt (Alarm.set_enable tt.(alarm) b).

Definition set_interval tt n := set_alarm tt (Alarm.set_interval tt.(alarm) n).

Definition set_trigger tt n := set_alarm tt (Alarm.set_trigger tt.(alarm) n).

(*TODO: ThreadTimer_initialize, encapsulation of Alarm_initialize*)

(*TODO: ThreadTimer_alarm*)

(****************************************************************)
(*The list of thread timers, which will be in a clock*)

Module ThreadTimer_obj <: DNode.

  Definition Obj := ThreadTimer.

  Definition eq_Obj (x y : ThreadTimer) :=
    beq_nat x.(alarm).(alarm_id) y.(alarm).(alarm_id).

  Definition A := nat.
  
  Definition test_Obj x n := beq_nat x.(alarm).(alarm_id) n.

End ThreadTimer_obj.

(*The cycled double linked list of alarm*)
Module TTL := CList ThreadTimer_obj.

Definition ThreadTimerList := TTL.CList ThreadTimer.

Definition get_threadtimer (ttl : ThreadTimerList)(ttid : nat) : option ThreadTimer :=
TTL.get_Obj ttl ttid.

Definition update_threadtimer (ttl : ThreadTimerList)(tt : ThreadTimer) : ThreadTimerList :=
TTL.update_Obj ttl tt.