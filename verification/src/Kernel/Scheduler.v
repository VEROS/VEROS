Require Import Scheduler_Implementation.

Record Scheduler := mkS {
  sched_imp : Scheduler_Implementation
}.

