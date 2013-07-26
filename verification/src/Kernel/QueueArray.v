Set Implicit Arguments.

Require Import Array.
Require Import Thread.

Import Vector.

Definition init_nil n := init n RunQueue_cstr.

Definition nth_q n (ba : array RunQueue n)(m : nat) :=
  Array.nth RunQueue_cstr ba (n-m).

Definition set_q n (ba : array RunQueue n)(m : nat)(q : RunQueue) :=
  set_value ba (n-m) q.

(*
 *try to remove a thread from the array of RunQueue
 *if the thread is in the array, its priority is the index of the queue in the array.
 *)
Definition remove_t n (ba : array RunQueue n)(t : Thread) : array RunQueue n. 
set (index := get_priority t).
exact (set_q ba index (TO.remove (nth_q ba index) t)).
Defined.