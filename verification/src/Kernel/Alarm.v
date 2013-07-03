Set Implicit Arguments.

Require Import List.

Record Alarm := mkALM{
  unique_id : nat;
  trigger : nat;
  interval : nat;
  enable : bool
}.

(*DO : Alarm construct func, ignore counter alarm data*)
Definition Alarm_cstr (uid t i : nat)(e : bool) : Alarm := 
  mkALM uid t i e.

Definition AlarmList := list Alarm.

(*DO : functions operating the list*)

(*Definition get_head(l : AlarmList) : Alarm := .

Definition get_tail()

Definition rem_head()

Definition rem_tail()
*)