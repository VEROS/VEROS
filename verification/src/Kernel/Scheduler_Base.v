Set Implicit Arguments.

Require Import Scheduler_SchedLock.
Require Import Thread.

Record Scheduler_Base := mksb{
  sched_lock : Scheduler_SchedLock;
  current_thread : Thread; 
  need_reschedule : bool;
  thread_switches : nat
}.

Definition get_current_thread (sb : Scheduler_Base) := sb.(current_thread).

Definition set_current_thread (sb : Scheduler_Base) t := 
  mksb sb.(sched_lock) t sb.(need_reschedule) sb.(thread_switches).

Definition set_need_reschedule sb := 
  mksb sb.(sched_lock) sb.(current_thread) true sb.(thread_switches).

Definition set_need_reschedule_t sb (t : Thread) := 
  mksb sb.(sched_lock) sb.(current_thread) true sb.(thread_switches). 

Definition get_need_reschedule sb := sb.(need_reschedule).

Definition clear_need_reschedule sb :=
  mksb sb.(sched_lock) sb.(current_thread) false sb.(thread_switches).

Definition get_thread_switches sb := sb.(thread_switches).

Definition set_thread_switches sb n := 
  mksb sb.(sched_lock) sb.(current_thread) sb.(need_reschedule) n.

Definition change_sched_lock sb sl :=
  mksb sl sb.(current_thread) sb.(need_reschedule) sb.(thread_switches).

Definition inc_sched_lock sb := 
  change_sched_lock sb (Scheduler_SchedLock.inc_sched_lock sb.(sched_lock)).

Definition zero_sched_lock sb := 
  change_sched_lock sb (Scheduler_SchedLock.zero_sched_lock sb.(sched_lock)).

Definition set_sched_lock sb n := 
  change_sched_lock sb (Scheduler_SchedLock.set_sched_lock sb.(sched_lock) n).

Definition get_sched_lock (sb : Scheduler_Base) :=
  (Scheduler_SchedLock.get_sched_lock sb.(sched_lock)).

Definition Scheduler_Base_cstr := 
  mksb Scheduler_SchedLock_cstr (Thread_cstr 0 0 0 0) false 0.