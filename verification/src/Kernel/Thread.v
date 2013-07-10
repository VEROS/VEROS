Set Implicit Arguments.

Require Import EqNat.
Require Import SchedThread.
Require Import DLClist.

Inductive ThreadState : Set :=
| RUNNING : ThreadState
| SLEEPING : ThreadState
| COUNTSLEEP : ThreadState
| SUSPENDED : ThreadState
| CREATING : ThreadState
| EXITED : ThreadState.

Inductive Reason : Set :=
| NONE : Reason
| WAIT : Reason
| DELAY : Reason
| TIMEOUT : Reason
| BREAK : Reason
| DESTRUCT : Reason
| EXIT : Reason
| DONE : Reason.

Record SleepWakeup := mkSW{

  sleep_reason : Reason;
  wake_reason : Reason;
  supend_count : nat;
  wakeup_count : nat

}.


Record Thread := mkThread{

  unique_id : nat; 
  timer_id : nat;
  state : ThreadState;
  wait_info : nat;
  sleep_wakeup : SleepWakeup;

  (*Inherited from SchedThread_Implementation*)
  sched_thread : SchedThread

}.



(********************************************************)
(*The double linked cycled list of thread*)

Module Thread_Obj <: DNode.

  Definition Obj := Thread.

  Definition eq_Obj (x y : Thread) :=
    beq_nat x.(unique_id) y.(unique_id).

End Thread_Obj.

Module TO := CList Thread_Obj.

Definition RunQueue := TO.CList Thread.