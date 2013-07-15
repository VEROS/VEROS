Set Implicit Arguments.

Record Alarm := mkALM{
  unique_id : nat;
  counter_id : nat;
  trigger : nat;
  interval : nat;
  enable : bool
}.

(*DO : Alarm construct func, ignore counter alarm data*)
Definition Alarm_cstr (uid t : nat) : Alarm := 
  mkALM uid t 0 0 false.

Definition set_enable a := 
  mkALM (unique_id a) (counter_id a) (trigger a) (interval a) true.

Variable A : Type.

Variable X : A.

(*call the alarm function, to be replaced with the real function*)
Definition alarm_call (a : A) : A := a.
