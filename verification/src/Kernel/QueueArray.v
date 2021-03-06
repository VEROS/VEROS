Set Implicit Arguments.

Add LoadPath "../HAL".

Require Import Array.
Require Import Thread.

Import Vector.

Definition init_nil n := init n ThreadQueue_cstr.

Definition nth_q n (ba : array ThreadQueue n)(m : nat) :=
  Array.nth ThreadQueue_cstr ba (n-m).

Definition set_q n (ba : array ThreadQueue n)(m : nat)(q : ThreadQueue) :=
  set_value ba (n-m) q.

(*
 *try to remove a thread from the array of RunQueue
 *if the thread is in the array, its priority is the index of the queue in the array.
 *)
Definition remove_t n (ba : array ThreadQueue n)(t : Thread) : array ThreadQueue n. 
set (index := get_priority t).
exact (set_q ba index (TO.remove (nth_q ba index) t)).
Defined.

Definition array_get_thread n (ba : array ThreadQueue n)(tid : nat) : option (nat*nat).
induction n as [|n' IHn']; [exact None| ].
  destruct (Thread.get_thread (hd ba) tid) as [a| ].
    exact (Some a).
    exact (IHn' (tl ba)).
Defined.

Definition array_get_thread_t n (ba : array ThreadQueue n)(tid : nat) : option Thread.
induction n as [|n' IHn']; [exact None| ].
  destruct (Thread.get_thread_t (hd ba) tid) as [t| ].
    exact (Some t).
    exact (IHn' (tl ba)).
Defined.