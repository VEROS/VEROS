Set Implicit Arguments.

Require Import EqNat.
Require Import Bool.
Require Import ThreadTimer.
Require Import DLClist.
Require Import NPeano.

Record Counter := mkCounter{
  
  unique_counter_id : nat;
  threadtimer_list : IDList;
  count : nat;
  increment : nat

}.

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

Definition set_threadtimer_list c il := 
  mkCounter c.(unique_counter_id) il c.(count) c.(increment).

(*if the ttid is in the list of this counter c then go for it in the real timerlist*)
Definition get_threadtimer c ttid ttl := 
  if (IL.inside c.(threadtimer_list) ttid)
  then ThreadTimer.get_threadtimer ttl ttid
  else None.

Definition synchronize (c : Counter)(ttid : nat)(ttl : ThreadTimerList) : ThreadTimerList.
destruct (get_threadtimer c ttid ttl) as [tt|]; [|exact ttl]. 
  set (interval := get_interval tt).
  destruct (interval) as [ | ]; [exact ttl|].
    set (d := (current_value c) + interval - (get_trigger tt)).
      case (ltb interval d).
        exact (update_threadtimer ttl (set_trigger tt (interval * (d-1)/interval))).
        exact ttl.
Defined.

Definition add_alarm (c : Counter)(ttid : nat)(ttl : ThreadTimerList) : Counter*ThreadTimerList.
destruct (ThreadTimer.get_threadtimer ttl ttid) as [tt|]; [|exact (c, ttl)].
set (tt' := set_enable tt true).
set (c' := set_threadtimer_list c (IL.add_tail (get_threadtimer_list c) ttid)). 
case (leb (get_trigger tt') c.(count)).
  (*TO_DO: alarm->alarm(alarm, alarm->data)*) 
  case ((negb (beq_nat (get_interval tt') 0)) && (get_enable tt')). 
    set (tt'' := set_trigger tt' ((get_trigger tt') + (get_interval tt'))).
    set (ttl' := synchronize c ttid (update_threadtimer ttl tt'')).
    exact (c', ttl').    
     
    exact (c, update_threadtimer ttl (set_enable tt' false)).
  exact (c', update_threadtimer ttl tt').
Defined.

Definition enable (c : Counter)(ttid : nat)(ttl : ThreadTimerList) : Counter*ThreadTimerList.
destruct (ThreadTimer.get_threadtimer ttl ttid) as [tt|]; [|exact (c, ttl)].
case (get_enable tt). 
  exact (c, ttl).
  (*TO_DO: lock unlock*)
  exact (add_alarm c ttid (synchronize c ttid ttl)).
Defined.

Definition rem_alarm (c : Counter)(ttid : nat)(ttl : ThreadTimerList) : Counter*ThreadTimerList.
destruct (get_threadtimer c ttid ttl) as [tt|]; [|exact (c, ttl)]. 
  set (c':= set_threadtimer_list c (IL.remove c.(threadtimer_list) ttid)).
  set (ttl' := update_threadtimer ttl (set_enable tt false)).
  exact (c', ttl').
Defined.

Definition disable (c : Counter)(ttid : nat)(ttl : ThreadTimerList) : Counter*ThreadTimerList.
destruct (get_threadtimer c ttid ttl) as [tt|]; [|exact (c, ttl)].
(*TO_DO: lock unlock*)
case (get_enable tt). 
  exact (rem_alarm c ttid ttl). 
  exact (c, ttl).
Defined.

Definition initialize (c : Counter)(ttid : nat)(ttl : ThreadTimerList)(t i : nat) : Counter*ThreadTimerList.
destruct (get_threadtimer c ttid ttl) as [tt|]; [|exact (c, ttl)].
assert (h : Counter * ThreadTimerList).
case (get_enable tt). 
  exact (rem_alarm c ttid ttl).
  exact (c, ttl).
destruct h as [c' ttl'].
  exact (add_alarm c' ttid (update_threadtimer ttl' (set_interval (set_trigger tt t) i))).
Defined.