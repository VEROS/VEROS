Set Implicit Arguments.

Require Import Scheduler_SchedLock.
Require Import Thread.

Record Scheduler_Base := mksb{

  sched_lock : Scheduler_SchedLock;
  current_thread : Thread;
  need_reschedule : bool
  (*thread_switches is abandoned*)

}.

(*DO : get_curreent_thread*)

(*DO : set_current_thread*)

(*DO : set_need_reschedule*)

(*DO : get_need_reschedule*)

(*DO : get_sched_lock*)

(*DO : clear_need_reschedule*)

(*DO : get_thread_switches*)
