Set Implicit Arguments.

Require Import Scheduler_SchedLock.

Record Scheduler_Base := mksb{
  sched_lock : Scheduler_SchedLock;
  (*the unique_id of a thread*)
  current_thread : nat; 
  need_reschedule : bool;
  thread_switches : nat
}.

(*DO : get_curreent_thread*)

(*DO : set_current_thread*)

(*DO : set_need_reschedule*)

(*DO : get_need_reschedule*)

(*DO : get_sched_lock*)
Definition get_sched_lock (sb : Scheduler_Base) :=
  (Scheduler_SchedLock.get_sched_lock (sched_lock sb)).

(*DO : clear_need_reschedule*)

(*DO : get_thread_switches*)
