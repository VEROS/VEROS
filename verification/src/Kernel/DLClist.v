Set Implicit Arguments.

Require Import List.


Module Type DNode.

  Parameter Obj : Type.

  Parameter eq_Obj : Obj -> Obj -> bool.

End DNode.


Module CList (Import M : DNode).

  Definition CList := list.
  
  Definition CList_cstr := (@nil Obj).
  
  Definition get_head (l : CList Obj) := hd_error l.
  
  Fixpoint get_tail (l : CList Obj) :=
    match l with
      | nil => error
      | x :: l' => match l' with
                     | nil => value x
                     | _ :: _ => get_tail l'
                   end
    end.
  
  Definition empty (l : CList Obj) :=
    match l with
      | nil => true
      | _ => false
    end.
  
  Fixpoint inside (l : CList Obj) (x : Obj) :=
    match l with
      | nil => false
      | y :: l' => if (eq_Obj x y) then true else (inside l' x)
    end.

  Definition add_head (l : CList Obj) (x : Obj) := x :: l.
  
  Definition rem_head (l : CList Obj) :=
    match l with
      | nil => (error, nil)
      | x :: l => (value x, l)
    end.
  
  Fixpoint add_tail (l : CList Obj) (x : Obj) :=
    match l with
      | nil => x :: nil
      | y :: l' => y :: (add_tail l' x)
    end.
  
  Fixpoint rem_tail (l : CList Obj) :=
    match l with
      | nil => (error, nil)
      | x :: l' => 
      match l' with
        | nil => (value x, l')
        | _ :: _ => (fst (rem_tail l'), (x :: snd (rem_tail l')))
      end
    end.
  
  Definition merge (l1 l2 : CList Obj) := l1 ++ l2.


  (*x should be in l, which is not checked in this function*)
  Fixpoint remove (l : CList Obj) (x : Obj) :=
    match l with
      | nil => nil
      | y :: l' => 
        if (eq_Obj x y) then l' else (y :: (remove l' x))
    end.

  Definition rotate (l : CList Obj) :=
    match l with
      | nil => nil
      | x :: l' => add_tail l' x
    end.


  (*x should be in l, which is not checked in this function*)
  Fixpoint split_from_x (l l' : CList Obj) (x : Obj) :=
    match l with
      | nil => (l, l')
      | y :: ll => 
        if (eq_Obj x y) then (l, l') else
          split_from_x ll (l' ++ (y :: nil)) x
    end.
        

  Definition to_head (l : CList Obj) (x : Obj) :=
    let two_list := split_from_x l nil x in
      (fst two_list) ++ (snd two_list).

  (*Suppose x in l, put y before x*)
  Fixpoint insert (l : CList Obj) (x y : Obj) :=
    match l with
      | nil => nil
      | z :: l' => 
        if (eq_Obj x z) then y :: l
          else z :: (insert l' x y)
    end.


End CList.


(* The followings are used for testing *)
(* Feel free to add test cases for the above functions*)
(*
Module M1 <: DNode.

  Definition Obj := nat.

  Fixpoint eq_Obj x y :=
    match x, y with
      | 0, 0 => true
      | S m, S n => eq_Obj m n
      | _, _ => false
    end.

End M1.

Module M2 := CList M1.

Import M2.

Eval compute in (to_head (1::2::3::4::nil) 4).

Eval compute in (remove (1::2::3::4::nil) 4).
*)
