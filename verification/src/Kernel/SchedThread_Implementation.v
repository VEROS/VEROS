Set Implicit Arguments.

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

Variable set_count : 
  SchedThread_Implementation -> nat -> SchedThread_Implementation.

Variable SchedThread_Implementation_cstr :
  nat -> SchedThread_Implementation.

(*TODO: function 'yield'*)

(*TODO : function 'rotate_queue'*)

(*TODO : function 'to_queue_head'*)

(*TODO : Definition timeslice_save*)

(*TODO : timeslice_restore*)

Definition timeslice_reset (r : SchedThread_Implementation) 
  (count : nat) :=
  mkSTI (priority r) (timeslice_enable r) count.

Variable timeslice_enable_fun : SchedThread_Implementation ->
  SchedThread_Implementation.

Variable timeslice_disable_fun : SchedThread_Implementation ->
  SchedThread_Implementation.





