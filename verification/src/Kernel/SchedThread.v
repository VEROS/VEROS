Set Implicit Arguments.

Require Import SchedThread_Implementation.

Record SchedThread := mkst {
  
  schedthread_imp : SchedThread_Implementation
  (*TODO: queue : Run_queue*)                    
}.

Definition SchedThread_cstr p := mkst (SchedThread_Implementation_cstr p).

(*TODO: get current_queue*)

(*TODO: remove*)

Definition timeslice_enable st :=
  SchedThread_Implementation.timeslice_enable st.(schedthread_imp).

Definition timeslice_disable st :=
  SchedThread_Implementation.timeslice_disable st.(schedthread_imp).

(*TODO: yield*)
