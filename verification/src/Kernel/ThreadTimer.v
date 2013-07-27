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

Definition set_alarm tt a := mkTT a tt.(thread_id). 

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

End ThreadTimer_obj.

(*The cycled double linked list of alarm*)
Module TTL := CList ThreadTimer_obj.

Definition ThreadTimerList := TTL.CList ThreadTimer.

Definition get_threadtimer (ttl : ThreadTimerList)(ttid : nat) : option ThreadTimer.
induction ttl as [|tt ttl' IHttl']; [exact None|].
  case (beq_nat ttid (get_timer_id tt)).
    exact (Some tt).  
    exact IHttl'.
Defined.

Definition update_threadtimer (ttl : ThreadTimerList)(tt : ThreadTimer) : ThreadTimerList.
induction ttl as [|tt' ttl' IHttl']; [exact nil|].
  case (ThreadTimer_obj.eq_Obj tt tt').  
    exact (cons tt ttl').
    exact (cons tt' IHttl').
Defined.
