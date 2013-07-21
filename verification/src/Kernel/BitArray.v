Set Implicit Arguments.

Require Import Array.
Import Vector.

(*Set 0 to the bit representing priority m*)
Definition set_0 n (ba : array bool n) (m : nat) :=
  set_value ba (n-m) false.

(*Set 1 to the bit representing priority m*) 
Definition set_1 n (ba : array bool n) (m : nat) :=
  set_value ba (n-m) true.


(*Construct a length-n vector with all bits 0*)
Definition init_0 n := init n false.

(*Get the mth element of a n-bit vector*)
Definition nth_b n (ba : array bool n) (m : nat) :=
  Array.nth false ba (n-m).

(*Least significant bit *)
Definition lsb n (ba : array bool n) : nat.
induction n as [|n rec].
 exact 1.

 set (h := hd ba).
 case_eq h; intro H.
  exact 0.

  exact (S (rec (tl ba))).

Defined.

 

 
 

 



(* Simpl test cases *)
(*
Require Import Bvector.
Eval compute in (set_0 [true;false;true] 0).

Eval compute in (set_1 [true;false;true] 1).

Eval compute in (init_0 5).

Eval compute in (nth_b [true;false;true;true;true] 1).

Eval compute in (lsb [false; false; false; true; false]).
*)