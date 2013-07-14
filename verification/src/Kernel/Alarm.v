Set Implicit Arguments.

Record Alarm := mkALM{
  unique_id : nat;
  counter_id : nat;
  trigger : nat;
  interval : nat;
  enable : bool
}.

(*DO : Alarm construct func, ignore counter alarm data*)
Definition Alarm_cstr (uid t : nat) : Alarm := 
  mkALM uid t 0 0 false.

Definition AlarmList := list Alarm.

(*DO : functions operating the list*)

Infix "::" := cons (at level 60, right associativity) : list_scope.
Delimit Scope list_scope with list.

Local Open Scope list_scope.

Definition get_head(l : AlarmList) : option Alarm := 
  match l with
  |nil => None
  |a :: _ => Some a
  end. 
  
Fixpoint get_tail(l : AlarmList) : option Alarm :=
  match l with
  |nil => None
  |a :: l' => match l' with
              |nil => Some a
              |_ :: _ => get_tail l'
              end
  end.            

Definition rem_head(l : AlarmList) : AlarmList :=
  match l with
  |nil => nil
  |_ :: l' => l'
  end.

Fixpoint rem_tail(l : AlarmList) : AlarmList :=
  match l with
  |nil => nil
  |a :: l' => match l' with
              |nil => nil
              |_ :: _ => a :: rem_tail l'
              end
  end.

