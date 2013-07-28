Set Implicit Arguments.

Require Import EqNat.
Require Import Bool.
Require Import ThreadTimer.
Require Import DLClist.
Require Import NPeano.

Record Counter := mkCounter{
  
  unique_counter_id : nat;
  threadtimer_list : ThreadTimerList;
  count : nat;
  increment : nat

}.

Definition set_ttl c ttl :=
  mkCounter c.(unique_counter_id) ttl c.(count) c.(increment).

Definition rem_alarm c a := 
  set_ttl c (TTL.remove (c.(threadtimer_list)) a).

Definition counter_cstr uid tl inc := mkCounter uid tl O inc.

Definition counter_cstr_default uid tl := mkCounter uid tl O (S O).

Definition current_value (c : Counter) := c.(count).

Definition current_value_lo c := c.(count) mod (2^32).

Definition current_value_hi c := c.(count) / (2^32).

Definition set_value c n := 
  mkCounter c.(unique_counter_id) c.(threadtimer_list) n c.(increment). 

(*TODO : tick*)

Definition get_counter_id c := c.(unique_counter_id).

Definition get_threadtimer_list c := c.(threadtimer_list).

Definition set_threadtimer_list c ttl := 
  mkCounter c.(unique_counter_id) ttl c.(count) c.(increment).

Definition get_threadtimer c ttid := ThreadTimer.get_threadtimer c.(threadtimer_list) ttid.

Definition update_threadtimer c tt := 
  set_threadtimer_list c (ThreadTimer.update_threadtimer c.(threadtimer_list) tt).

Definition synchronize (c : Counter)(tt : ThreadTimer) : ThreadTimer. 
set (interval := get_interval tt).
destruct (interval) as [ | ]; [exact tt|].
  set (d := (current_value c) + interval - (get_trigger tt)).
  case (ltb interval d).
    exact (set_trigger tt (interval * (d-1)/interval)).
    exact tt.
Defined.

Definition add_alarm (c : Counter)(tt : ThreadTimer) : Counter.
set (tt' := set_enable tt true). assert(tt'' : ThreadTimer).
destruct (leb (get_trigger tt') c.(count)) as [ | ]; [ |exact tt'].
  (*TODO: alarm->alarm(alarm, alarm->data)*) 
  case ((negb (beq_nat (get_interval tt') 0)) && (get_enable tt')). 
    set (tt1 := set_trigger tt' ((get_trigger tt') + (get_interval tt'))).  
    exact (synchronize c tt1).    
     
    exact (set_enable tt' false).
exact (set_threadtimer_list c (TTL.add_tail (get_threadtimer_list c) tt'')).
Defined.

Definition enable (c : Counter)(tt : ThreadTimer) : Counter :=
(*TODO: lock unlock*)
if (get_enable tt) then c else add_alarm c (set_enable (synchronize c tt) true).

Definition disable (c : Counter)(tt : ThreadTimer) : Counter :=
(*TODO: lock unlock*)
if (get_enable tt) then rem_alarm c tt else c.
