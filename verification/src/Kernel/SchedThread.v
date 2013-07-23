Set Implicit Arguments.

Require Import Constant.
Require Import SchedThread_Implementation.

Record SchedThread := mkst {
  schedthread_imp : SchedThread_Implementation;
  queue : nat (*index in run_queue_array*)
}.

Definition SchedThread_cstr p := mkst (SchedThread_Implementation_cstr p) PRIORITIES.

Definition get_current_queue st := st.(queue).

Definition set_queue st index := mkst st.(schedthread_imp) index.

(*indicate that the thread is removed from some run_queue*)
Definition remove st := set_queue st PRIORITIES.

Definition timeslice_enable st :=
  mkst (SchedThread_Implementation.timeslice_enable st.(schedthread_imp)) st.(queue).

Definition timeslice_disable st :=
  mkst (SchedThread_Implementation.timeslice_disable st.(schedthread_imp)) st.(queue).

Definition timeslice_reset st :=
  mkst (SchedThread_Implementation.timeslice_reset st.(schedthread_imp)) st.(queue).

(*TODO: yield*)

Definition get_priority st :=
  st.(schedthread_imp).(priority).

Definition addthread st := set_queue st (get_priority st). 