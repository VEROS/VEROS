Set Implicit Arguments.

Require Import EqNat.
Require Import ThreadTimer.
Require Import DLClist.
Require Import NPeano.

Record Counter := mkcounter{
  
  unique_counter_id : nat;
  threadtimer_list : ThreadTimerList;
  count : nat;
  increment : nat

}.

(*DO : add_alarm*)

(*DO : rem_alarm*)
Definition rem_alarm c a := 
  mkcounter c.(unique_counter_id) (TTL.remove (c.(threadtimer_list)) a) c.(count) c.(increment).

(*DO : Counter_cstr*)
Definition counter_cstr uid tl inc := mkcounter uid tl O inc.

Definition counter_cstr_default uid tl := mkcounter uid tl O (S O).

(*DO : current_value*)
Definition current_value (c : Counter) := c.(count).

(*DO : current_value_lo*)
Definition current_value_lo c := c.(count) mod (2^32).

(*DO : current_value_hi*)
Definition current_value_hi c := c.(count) / (2^32).

(*DO : set_value*)
Definition set_value c n := 
  mkcounter c.(unique_counter_id) c.(threadtimer_list) n c.(increment). 

(*TODO : tick*)

Definition get_counter_id c := c.(unique_counter_id).

Definition get_counter_threadtimer_list c := c.(threadtimer_list).

