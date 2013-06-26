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

Variable set_count : 
  SchedThread_Implementation -> nat -> SchedThread_Implementation.

Variable SchedThread_Implementation_cstr :
  nat -> SchedThread_Implementation.

