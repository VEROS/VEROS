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

(*tick : defined in Kernel.v*)

Definition get_counter_id c := c.(unique_counter_id).

Definition get_threadtimer_list c := c.(threadtimer_list).

Definition set_threadtimer_list c il := 
  mkCounter c.(unique_counter_id) il c.(count) c.(increment).

