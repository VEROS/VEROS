Set Implicit Arguments.

Require Import Constant.
Require Import SchedThread_Implementation.
Require Import SuspendQueue.

Record SchedThread := mkst {
  schedthread_imp : SchedThread_Implementation;
  queue : SuspendQueue
}.

Definition SchedThread_cstr p := mkst (SchedThread_Implementation_cstr p) NULL.

Definition get_current_queue st := st.(queue).

Definition set_current_queue st q := mkst st.(schedthread_imp) q.

Definition set_queue st sq := mkst st.(schedthread_imp) sq.

Definition timeslice_enable st :=
  mkst (SchedThread_Implementation.timeslice_enable st.(schedthread_imp)) st.(queue).

Definition timeslice_disable st :=
  mkst (SchedThread_Implementation.timeslice_disable st.(schedthread_imp)) st.(queue).

Definition timeslice_reset st :=
  mkst (SchedThread_Implementation.timeslice_reset st.(schedthread_imp)) st.(queue).

Definition get_priority st := st.(schedthread_imp).(priority). 

Definition set_priority st n := 
  mkst (SchedThread_Implementation.set_priority st.(schedthread_imp) n) st.(queue).

Definition timeslice_save st new_count := 
  mkst (SchedThread_Implementation.timeslice_save st.(schedthread_imp) new_count) st.(queue).

Definition get_timeslice_count st := SchedThread_Implementation.get_timeslice_count st.(schedthread_imp).

(*remove : defined in Kernel.v*)