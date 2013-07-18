Set Implicit Arguments.

Require Import SchedThread_Implementation.

Record SchedThread := mkst {
  
  schedthread_imp : SchedThread_Implementation
  (*queue : Run_queue*)                    
}.

Definition SchedThread_cstr p := mkst (SchedThread_Implementation_cstr p).