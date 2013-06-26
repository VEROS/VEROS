Set Implicit Arguments.


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


