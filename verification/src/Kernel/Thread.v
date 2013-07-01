Set Implicit Arguments.

Require Import SchedThread_Implementation.

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
  state : ThreadState;
  wait_info : nat;
  sleep_wakeup : SleepWakeup;

  (*Inherited from SchedThread_Implementation*)
  sched_thread : SchedThread_Implementation

}.




Definition ThreadQueue := list Thread.


Definition RunQueue := list Thread.




