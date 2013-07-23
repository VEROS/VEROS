Set Implicit Arguments.

Require Import Scheduler_Implementation.
Require Import Thread.
Require Import NPeano.

Record Scheduler := mkS {
  sched_imp : Scheduler_Implementation
}.

Definition lock s := mkS (Scheduler_Implementation.inc_sched_lock s.(sched_imp)).

Definition get_current_thread s := Scheduler_Implementation.get_current_thread s.(sched_imp).

Definition get_need_reschedule s := Scheduler_Implementation.get_need_reschedule s.(sched_imp).

Definition schedule s := Scheduler_Implementation.schedule s.(sched_imp).

Definition set_sched_lock s n := mkS (Scheduler_Implementation.set_sched_lock s.(sched_imp) n).

Definition zero_sched_lock s := mkS (Scheduler_Implementation.zero_sched_lock s.(sched_imp)).

Definition get_sched_lock s:= Scheduler_Implementation.get_sched_lock s.(sched_imp).

Definition clear_need_reschedule s := mkS (Scheduler_Implementation.clear_need_reschedule s.(sched_imp)).

(*TODO: unlock inner*)

(*TODO: unlock*)

(*TODO: reschedule*)

(*TODO: unlock_reschedule*)

Definition unlock_simple s := 
  if (ltb 1 (get_sched_lock s)) 
  then set_sched_lock s ((get_sched_lock s) - 1)
  else zero_sched_lock s.

(*TODO: start*)

(*TODO: start_cpu*)