Set Implicit Arguments.
(*
Require Import Scheduler_Implementation.
*)
Require Import Constant.

Record SchedThread_Implementation := mkSTI {

  priority : nat;

  (*CYGSEM_KERNEL_SCHED_TIMESILEC_ENABLE*)
  timeslice_enabled : bool;

  (*CYGSEM_KERNEL_SCHED_TIMESLICE*)
  timeslice_count : nat

}.

Definition set_priority (r : SchedThread_Implementation) (p : nat) :=
  mkSTI p r.(timeslice_enabled) r.(timeslice_count).

Definition set_enable (r : SchedThread_Implementation) (en : bool) :=
  mkSTI r.(priority) en r.(timeslice_count).

Definition set_count (r : SchedThread_Implementation) (c : nat) := 
  mkSTI r.(priority) r.(timeslice_enabled) c.

Definition SchedThread_Implementation_cstr (p : nat) :=
  mkSTI p true 0.

(*Defined in Scheduler.v : function 'to_queue_head'*)

Definition timeslice_save (sti : SchedThread_Implementation) new_count := mkSTI sti.(priority) sti.(timeslice_enabled) new_count.

Definition get_timeslice_count sti := sti.(timeslice_count). 

Definition timeslice_reset (r : SchedThread_Implementation) :=
  mkSTI r.(priority) r.(timeslice_enabled) CYGNUM_KERNEL_SCHED_TIMESLICE_TICKS.

Definition timeslice_enable (r: SchedThread_Implementation) := 
  set_enable r true.

Definition timeslice_disable (r : SchedThread_Implementation) := 
  set_enable r false.





