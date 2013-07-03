Set Implicit Arguments.

Require Import List.

Variable A : Type.

Definition queue := list.

(*Need to be checked : put the element x at the head of the queue*)
Definition enqueue (q : queue A) (x : A) := x :: q.

(*Need to be checked : return the queue removing the last element*)
Fixpoint dequeue (q : queue A) :=
  match q with 
    | nil => nil
    | x :: l => x :: dequeue l
  end.

(*DO : set_thread_queue*)

(*DO : highpri*)

(*DO : remove*)

(*DO : empty*)

(*DO : insert*)

(*DO : add_tail*)

(*DO : get_head*)