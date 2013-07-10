Set Implicit Arguments.

Require Import SchedThread_Implementation.

Record SchedThread := mkst {
  
  schedthread_imp : SchedThread_Implementation

}.

