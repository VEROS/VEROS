Require Import Vector.

Set Implicit Arguments.

Section UsefulDef.
  
  Variable A : Type.
  Variable a : A.
  
  Definition vec            := t A.
  Definition vnil           := nil A.
  Definition vcons          := cons A.
  Notation " ∅ "            := vnil.
  Notation " x ⋈ v "        := (vcons x v) (at level 31).
  Notation "[ x , .. , y ]" := (vcons x .. (vcons y vnil) ..).
 

  Definition v_hd n (v : vec (S n)) := hd v.
  Definition v_tl n (v : vec (S n)) := tl v.
  Notation " v ▷ "                  := (v_hd v) (at level 42).
  Notation " v ◁ "                  := (v_tl v) (at level 41).



  Definition nth n (v : vec n) : nat -> A.
  induction n as [|n rec]; intros m.
   exact a.
  
   destruct m as [|m].
    exact (v ▷).

    exact (rec (v ◁) m).
  Defined.
  Notation " v @ m " := (nth v m) (at level 21).

  Definition add n (v : vec n) (t : A) := shiftin t v.
  Definition remove n (v : vec (S n))  := shiftout v.

End UsefulDef.

