Set Implicit Arguments.

Require Import BitArray.
Require Import Array.

Require Import Scheduler_Base.
Require Import Thread.

Definition PRIORITIES := 32.

Record Scheduler_Implementation := mkSI{

  scheduler_base : Scheduler_Base;
  
  queue_map : array bool PRIORITIES;

  run_queue : list RunQueue;

  timeslice_count : nat

}.

Definition get_timeslice_count si := si.(timeslice_count).

Definition set_timeslice_count si count := 
  mkSI si.(scheduler_base) si.(queue_map) si.(run_queue) count.

(*TODO: set_idle_thread*)

(*TODO: time_slice_cpu*)

(*TODO: time_slice*)

Definition CYGNUM_KERNEL_SCHED_TIMESLICE_TICKS := 1.

Definition Scheduler_Implementation_cstr := 
  mkSI (set_need_reschedule Scheduler_Base_cstr true) (init_0 32) nil 
       CYGNUM_KERNEL_SCHED_TIMESLICE_TICKS.

(*DO: schedule*)