Set Implicit Arguments.

Require Import Vector.

Section AbsTypeArray.

  Variable ele : Type.
  Variable default : ele.
  
  Definition array := t.
  
  Definition set_rec n (a : array ele n) (m : nat) (e : ele) : 
    array ele n.
  revert m; induction n as [|n rec]; intro m.
   exact a.
   
   destruct m as [|m].
    exact (cons ele e n (tl a)).
  
    exact (cons ele (hd a) n (rec (tl a) m)).
  Defined.

  Definition set_value n (a : array ele n) (m : nat) (e : ele) :=
    set_rec a (n-m) e.
  
  Fixpoint init n (e : ele) : array ele n :=
    match n with
      | 0 => (nil ele)
      | S n => cons ele e n (init n e)
    end.
  
  Definition nth_rec n (a : array ele n) (m : nat) : ele.
   revert m; induction n as [|n rec]; intros.
    exact default.
  
    destruct m as [|m].
     exact (hd a).
  
     exact (rec (tl a) m).
   Defined.

   Definition nth n (a : array ele n) (m : nat) :=
     nth_rec a (n-m).

End AbsTypeArray.





