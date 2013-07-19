Set Implicit Arguments.
(*
Require Import Scheduler_Implementation.
*)
Variable CYGNUM_KERNEL_SCHED_TIMESLICE_TICKS : nat.

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

(*TODO: function 'yield'*)

(*TODO : function 'rotate_queue'*)

(*TODO : function 'to_queue_head'*)

(*DO : Definition timeslice_save*)
(*
Definition timeslice_save (sti : SchedThread_Implementation) (si : Scheduler_Implementation) := mkSTI (priority r) (timeslice_enable r) (get_timeslice_count si).
*)
(*DO : timeslice_restore*)
(*
Definition timeslice_restore (sti : SchedThread_Implementation) (si : Scheduler_Implementation) := set_timeslice_count si (timeslice_count).
*)
Definition timeslice_reset (r : SchedThread_Implementation) 
  (count : nat) :=
  mkSTI r.(priority) r.(timeslice_enabled) count.

Definition timeslice_enable (r: SchedThread_Implementation) := 
  set_enable r true.

Definition timeslice_disable (r : SchedThread_Implementation) := 
  set_enable r false.





