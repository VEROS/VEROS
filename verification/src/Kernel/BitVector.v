Set Implicit Arguments.

Require Import Bvector.


(*Set 0 to the bit representing priority m*)
Definition set_0_rec n (bv : Bvector n) (m : nat) : Bvector n.
revert m; induction n as [|n rec]; intro m.
 exact bv.

 destruct m as [|m].
  exact (Bcons false n (Bhigh n bv)).

  exact (Bcons (Blow n bv) n (rec (Bhigh n bv) m)).
Defined.

Definition set_0 n (bv : Bvector n) (m : nat) :=
  set_0_rec bv (n-m).

(*Set 1 to the bit representing priority m*) 
Definition set_1_rec n (bv : Bvector n) (m : nat) : Bvector n.
revert m; induction n as [|n rec]; intro m.
 exact bv.

 destruct m as [|m].
  exact (Bcons true n (Bhigh n bv)).

  exact (Bcons (Blow n bv) n (rec (Bhigh n bv) m)).
Defined.

Definition set_1 n (bv : Bvector n) (m : nat) :=
  set_0_rec bv (n-m).


(*Construct a length-n vector with all bits 0*)
Fixpoint init_0 n :=
  match n with
    | 0 => Bnil
    | S n => Bcons false n (init_0 n)
  end.


(*Get the mth element of a n-bit vector*)
Definition nth_rec n (bv : Bvector n) (m : nat) : bool.
revert m; induction n as [|n rec]; intros.
 exact true.

 destruct m as [|m].
  exact (Blow n bv).

  exact (rec (Bhigh n bv) m).
Defined.
 