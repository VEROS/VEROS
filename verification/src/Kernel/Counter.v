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

(*DO : add_alarm*)

(*DO : rem_alarm*)

Definition rem_alarm c a := 
  mkcounter c.(unique_counter_id) (TTL.remove (c.(threadtimer_list)) a) c.(counter) c.(increment).

(*DO : Counter_cstr*)
Definition counter_cstr uid tl inc := mkcounter uid tl O inc.

Definition counter_cstr_default uid tl := mkcounter uid tl O (S O).

(*DO : current_value*)
Definition current_value (c : Counter) := c.(counter).

(*DO : current_value_lo*)

(*DO : current_value_hi*)

(*DO : set_value*)

(*TODO : tick*)