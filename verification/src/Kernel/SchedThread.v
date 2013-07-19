Set Implicit Arguments.

Require Import SchedThread_Implementation.

Record SchedThread := mkst {
  
  schedthread_imp : SchedThread_Implementation
  (*TODO: queue : Run_queue*)                    
}.

Definition SchedThread_cstr p := mkst (SchedThread_Implementation_cstr p).

(*TODO: get current_queue*)

(*TODO: remove*)

Definition SchedTread_timeslice_enable st :=
  SchedTread_Implementation_timeslice_enable st.(schedthread_imp).

Definition SchedTread_timeslice_disable st :=
  SchedTread_Implementation_timeslice_disable st.(schedthread_imp).

(*TODO: yield*)
