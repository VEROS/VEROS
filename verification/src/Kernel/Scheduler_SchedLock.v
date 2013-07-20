Set Implicit Arguments.

Record Scheduler_SchedLock := mkss{
  
  sched_lock : nat

}.

Definition Scheduler_SchedLock_cstr := mkss 1.

Definition inc_sched_lock ss := mkss (S ss.(sched_lock)).

Definition zero_sched_lock (ss : Scheduler_SchedLock) := mkss O.

Definition set_sched_lock (ss : Scheduler_SchedLock) sl := mkss sl.

Definition get_sched_lock (ss : Scheduler_SchedLock) := ss.(sched_lock). 
