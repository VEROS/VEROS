Set Implicit Arguments.

Record Alarm := mkALM{
  alarm_id : nat;
  counter_id : nat;
  trigger : nat;
  interval : nat;
  enable : bool
}.

(*DO : Alarm construct func, ignore counter alarm data*)
Definition Alarm_cstr (aid t : nat) : Alarm := 
  mkALM aid t 0 0 false.

Definition set_enable a b := 
  mkALM a.(alarm_id) a.(counter_id) a.(trigger) a.(interval) b.

Definition get_enable a := a.(enable).

Definition get_interval a := a.(interval).

Definition get_trigger a := a.(trigger).

Definition set_interval a n := 
  mkALM a.(alarm_id) a.(counter_id) a.(trigger) n a.(enable).
  
Definition set_trigger a n :=
  mkALM a.(alarm_id) a.(counter_id) n a.(interval) a.(enable).

(*TODO: Alarm_initialize*)

(*TODO: enable*)

(*TODO: disable*)

Definition get_times a := (a.(trigger), a.(interval)).

Variable A : Type.

Variable X : A.

(*call the alarm function, to be replaced with the real function*)
Definition alarm_call (a : A) : A := a.

