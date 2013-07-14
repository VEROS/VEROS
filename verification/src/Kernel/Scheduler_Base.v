Set Implicit Arguments.

Require Import Scheduler_SchedLock.

Record Scheduler_Base := mksb{
  sched_lock : Scheduler_SchedLock;
  (*the unique_id of a thread*)
  current_thread : nat; 
  need_reschedule : bool;
  thread_switches : nat
}.

Definition get_current_thread (sb : Scheduler_Base) : nat := current_thread sb.

Definition set_current_thread (sb : Scheduler_Base)(tid : nat) := 
  mksb (sched_lock sb) tid (need_reschedule sb) (thread_switches sb).

Definition set_need_reschedule sb b := 
  mksb (sched_lock sb) (current_thread sb) b (thread_switches sb).

Definition get_need_reschedule sb := need_reschedule sb.

Definition get_sched_lock (sb : Scheduler_Base) :=
  (Scheduler_SchedLock.get_sched_lock (sched_lock sb)).

Definition clear_need_reschedule sb :=
  mksb (sched_lock sb) (current_thread sb) false (thread_switches sb).

Definition get_thread_switches sb := thread_switches sb.