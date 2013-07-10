Set Implicit Arguments.

Record Alarm := mkALM{
  unique_id : nat;
  counter_id : nat;
  trigger : nat;
  interval : nat;
  enable : bool
}.

(*DO : Alarm construct func, ignore counter alarm data*)
Definition Alarm_cstr (uid cid : nat) : Alarm := 
  mkALM uid cid 0 0 false.