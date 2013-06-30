Set Implicit Arguments.

Record Alarm := mkALM{
  unique_id : nat;
  trigger : nat;
  interval : nat;
  enable : bool
}.

(*DO : Alarm construct func, ignore counter alarm data*)
Definition Alarm_cstr (uid t i : nat)(e : bool) : Alarm := mkALM uid t i e.
