Set Implicit Arguments.

Require Import Scheduler_Implementation.

Variable CYGNUM_KERNEL_SCHED_TIMESLICE_TICKS : nat.

Record SchedThread_Implementation := mkSTI {

  priority : nat;

  (*CYGSEM_KERNEL_SCHED_TIMESILEC_ENABLE*)
  timeslice_enable : bool;

  (*CYGSEM_KERNEL_SCHED_TIMESLICE*)
  timeslice_count : nat

}.

Definition set_priority (r : SchedThread_Implementation) (p : nat) :=
  mkSTI p (timeslice_enable r) (timeslice_count r).

Definition set_enable (r : SchedThread_Implementation) (en : bool) :=
  mkSTI (priority r) en (timeslice_count r).

Definition set_count (r : SchedThread_Implementation) (c : nat) := 
  mkSTI (priority r) (timeslice_enable r) c.

Definition SchedThread_Implementation_cstr (p : nat) :=
  mkSTI p true 0.

(*TODO: function 'yield'*)

(*TODO : function 'rotate_queue'*)

(*TODO : function 'to_queue_head'*)

(*DO : Definition timeslice_save*)
Definition timeslice_save (sti : SchedThread_Implementation) (si : Scheduler_Implementation):= mkSTI (priority r) (timeslice_enable r) (get_timeslice_count si).

(*DO : timeslice_restore*)

Definition timeslice_reset (r : SchedThread_Implementation) 
  (count : nat) :=
  mkSTI (priority r) (timeslice_enable r) count.

Definition timeslice_enable_fun (r: SchedThread_Implementation) := 
  set_enable r true.

Definition timeslice_disable_fun (r : SchedThread_Implementation) := 
  set_enable r false.





