Set Implicit Arguments.
Require Import Queue.
Require Import BitVector.

Section AlarmAndTimer.

 Record Alarm := mkALM{
   unique_id : nat;
   trigger : nat;
   interval : nat;
   enable : bool
 }.

 (*DO : Alarm construct func, ignore counter alarm data*)
 Definition Alarm_cstr (uid t i : nat)(e : bool) : Alarm := 
   mkALM uid t i e.

 Definition AlarmList :=  queue Alarm.

 (*Definition get_head(l : AlarmList) : Alarm := .

    Definition get_tail()
    
    Definition rem_head()
    
    Definition rem_tail()  *)

 Record ThreadTimer := mkTT{ 
   alarm : Alarm;
   thread_id : nat
 }.

 Definition Thread_Timer_cstr (r : ThreadTimer) (th : nat) :=
   mkTT (alarm r) th.

End AlarmAndTimer.


Section CounterAndClock.
  
  Record Counter := mkcounter{
    Alarm_List : AlarmList;
    counter : nat;
    increment : nat
  }.

  (*DO : add_alarm*)
  
  (*DO : rem_alarm*)
  
  (*DO : Counter_cstr*)
  
  (*DO : current_value*)
  Definition current_value (c : Counter) := (counter c).

  (*DO : current_value_lo*)

  (*DO : current_value_hi*)

  (*DO : set_value*)

  (*TODO : tick*)


  Record Resolution := mkrl{
    dividend : nat;
    divisor : nat
  }.

  Record Clock := mkclk{
    clock_counter : Counter;
    resolution : Resolution
  }.

  (*DO : Clock_cstr*)

  (*DO : set_resolution*)

  (*DO : get_resolution*)