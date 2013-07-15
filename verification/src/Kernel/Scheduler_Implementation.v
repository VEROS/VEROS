Set Implicit Arguments.

Require Import BitVector.
Import Bvector.

Require Import Scheduler_Base.
Require Import Thread.


Record Scheduler_Implementation := mkSI{

  scheduler_base : Scheduler_Base;
  
  queue_map : Bvector 32;

  run_queue : list RunQueue;

  timeslice_count : nat

}.

Definition get_timeslice_count si := timeslice_count si.

Definition set_timeslice_count si count := mkSI (scheduler_base si) (queue_map si) (run_queue si) count.