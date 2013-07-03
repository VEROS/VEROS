Set Implicit Arguments.

Require Import Alarm.

Record Counter := mkcounter{
  
  Alarm_List : AlarmList;
  counter : nat;
  increment : nat

}.

(*DO : add_alarm*)

(*DO : rem_alarm*)

(*DO : Counter_cstr*)

(*DO : current_value*)
Definition current_value (c : Counter) := (counter c).

(*DO : current_value_lo*)

(*DO : current_value_hi*)

(*DO : set_value*)

(*TODO : tick*)