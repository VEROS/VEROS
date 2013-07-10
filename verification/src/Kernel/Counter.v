Set Implicit Arguments.


Require Import EqNat.
Require Import ThreadTimer.
Require Import DLClist.

Record Counter := mkcounter{
  
  unique_counter_id : nat;
  threadtimer_list : ThreadTimerList;
  counter : nat;
  increment : nat

}.

Print Alarm.

(*DO : add_alarm*)

(*DO : rem_alarm*)

(*DO : Counter_cstr*)

(*DO : current_value*)
Definition current_value (c : Counter) := c.(counter).

(*DO : current_value_lo*)

(*DO : current_value_hi*)

(*DO : set_value*)

(*TODO : tick*)