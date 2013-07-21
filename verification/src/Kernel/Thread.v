Set Implicit Arguments.

Require Import EqNat.

Require Import SchedThread.

Require Import DLClist.
Require Import ThreadTimer.

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
  suspend_count : nat;
  wakeup_count : nat

}.

Definition SleepWakeup_set_wake_reason sw wr :=
  mkSW NONE wr sw.(suspend_count) sw.(wakeup_count).

Definition SleepWakeup_set_sleep_reason sw sr :=
  mkSW sr NONE sw.(suspend_count) sw.(wakeup_count).

Record Thread := mkThread{

  unique_id : nat; 
  timer : ThreadTimer;
  state : ThreadState;
  wait_info : nat;
  sleepwakeup : SleepWakeup;

  (*Inherited from SchedThread_Implementation*)
  schedthread : SchedThread

}.

Definition set_schedthread t ss := 
  mkThread t.(unique_id) t.(timer) t.(state) t.(wait_info) t.(sleepwakeup) ss.

(*Ignored init_context(this) in Thread.cxx line 218
  Nothing to do for scheduler.register_thread
  need to add this thread to run_queue in SchedThread*)
Definition Thread_cstr tid aid cid p := 
  mkThread tid (ThreadTimer_cstr aid cid tid) SUSPENDED 0 (mkSW NONE NONE 1 0) (SchedThread_cstr p).

(*TODO: reinitialize*)

(*TODO: to_queue_head*)

(*TODO: wake*)

(*TODO: counted_wake*)

(*TODO: cancel_counted_wake*)

(*TODO: suspend*)

(*TODO: resume*)

(*TODO: release*)

(*TODO: kill*)

(*TODO: force_resume*)

Definition get_state t := t.(state).

Definition set_wait_info t wi := 
  mkThread t.(unique_id) t.(timer) t.(state) wi t.(sleepwakeup) t.(schedthread).

Definition get_wait_info t := t.(wait_info).

(*TODO: delay*)

(*TODO: set_priority*)

Definition get_priority t := SchedThread.get_priority t.(schedthread).

Definition get_current_priority t := get_priority t.

Definition get_sleep_reason t := t.(sleepwakeup).(sleep_reason).

Definition set_wake_reason t wr :=
  mkThread t.(unique_id) t.(timer) t.(state) t.(wait_info) 
    (SleepWakeup_set_wake_reason t.(sleepwakeup) wr) t.(schedthread).

Definition set_wake_reason_none t := set_wake_reason t NONE.

Definition get_wake_reason t := t.(sleepwakeup).(wake_reason).

Definition get_unique_id t := t.(unique_id).

(*TODO: sleep*)

(*TODO: counted_sleep*)

(*TODO: counted_sleep_delay*)

(*TODO: exit*)

(*TODO: yield*)

(*TODO: rotate_queue*)

(*TODO: self*)

Definition set_sleep_reason t sr := 
  mkThread t.(unique_id) t.(timer) t.(state) t.(wait_info) 
    (SleepWakeup_set_sleep_reason t.(sleepwakeup) sr) t.(schedthread).

Definition set_sleep_reason_wait t := set_sleep_reason t WAIT.

(*TODO: set_timer*)

(*TODO: clear_timer*)


Definition timeslice_reset t := 
  set_schedthread t (SchedThread.timeslice_reset t.(schedthread)).

(********************************************************)
(*The double linked cycled list of thread*)

Module Thread_Obj <: DNode.

  Definition Obj := Thread.

  Definition eq_Obj (x y : Thread) :=
    beq_nat x.(unique_id) y.(unique_id).

End Thread_Obj.

Module TO := CList Thread_Obj.

Definition RunQueue := TO.CList Thread.

Definition RunQueue_cstr := @nil Thread.

