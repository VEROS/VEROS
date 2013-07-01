Set Implicit Arguments.

Record Alarm := mkALM{
  unique_id : nat;
  trigger : nat;
  interval : nat;
  enable : bool
}.

(*DO : Alarm construct func, ignore counter alarm data*)
<<<<<<< HEAD


Definition AlarmList := list Alarm.

(*TODO : functions operating the list*)

=======
Definition Alarm_cstr (uid t i : nat)(e : bool) : Alarm := mkALM uid t i e.
>>>>>>> a79dfd8f04ffa9fb98920cd200179e0321bf0dbb
