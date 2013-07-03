Set Implicit Arguments.

Require Import BitVector.
Import Bvector.

Require Import Scheduler_Base.
Require Import Thread.


Record Scheduler_Implementation := mkSI{

  scheduler_base : Scheduler_Base;
  
  queue_map : Bvector 32;

  run_queue : list ThreadQueue;

  timeslice_count : nat

}.
