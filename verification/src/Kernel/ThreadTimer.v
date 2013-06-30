Set Implicit Arguments.

Require Import Alarm.

Record ThreadTimer := mkTT{
  
  alarm : Alarm;
  thread_id : nat

}.

Definition Thread_Timer_cstr (r : ThreadTimer) (th : nat) :=
  mkTT (alarm r) th.