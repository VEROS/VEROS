
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

Definition SleepWakeup_set_suspend_count sw sc :=
  mkSW sw.(sleep_reason) sw.(wake_reason) sc sw.(wakeup_count).

Definition SleepWakeup_set_wakeup_count sw wc :=
   mkSW sw.(sleep_reason) sw.(wake_reason) sw.(wakeup_count) wc.

Record Thread := mkThread{

  unique_id : nat; 
  timer_id : nat;
  state : ThreadState;
  wait_info : nat;
  sleepwakeup : SleepWakeup;

  (*Inherited from SchedThread_Implementation*)
  schedthread : SchedThread

}.

Definition get_suspend_count t := t.(sleepwakeup).(suspend_count).

Definition set_suspend_count t n := 
  mkThread t.(unique_id) t.(timer_id) t.(state) t.(wait_info) 
    (SleepWakeup_set_suspend_count t.(sleepwakeup) n) t.(schedthread).

Definition set_schedthread t ss := 
  mkThread t.(unique_id) t.(timer_id) t.(state) t.(wait_info) t.(sleepwakeup) ss.

Definition timeslice_save t new_count := 
  set_schedthread t (SchedThread.timeslice_save t.(schedthread) new_count).

Definition get_timeslice_count t := SchedThread.get_timeslice_count t.(schedthread).

(*Ignored init_context(this) in Thread.cxx line 218
  Nothing to do for scheduler.register_thread
  need to add this thread to run_queue in SchedThread*)
Definition Thread_cstr tid aid p := 
  mkThread tid aid SUSPENDED 0 (mkSW NONE NONE 1 0) (SchedThread_cstr p).

(*TODO: reinitialize*)

(*Defined in Scheduler.v: to_queue_head*)

(*TODO: wake*)

(*TODO: counted_wake*)

(*TODO: cancel_counted_wake*)

(*TODO: suspend*)

(*Defined in Scheduler.v: resume*)

(*TODO: release*)

(*TODO: kill*)

(*TODO: force_resume*)

Definition get_state t := t.(state).

Definition set_wait_info t wi := 
  mkThread t.(unique_id) t.(timer_id) t.(state) wi t.(sleepwakeup) t.(schedthread).

Definition get_wait_info t := t.(wait_info).

(*TODO: delay*)

(*TODO: set_priority*)

Definition get_priority t := SchedThread.get_priority t.(schedthread).

Definition get_current_priority t := get_priority t.

Definition get_sleep_reason t := t.(sleepwakeup).(sleep_reason).

Definition set_wake_reason t wr :=
  mkThread t.(unique_id) t.(timer_id) t.(state) t.(wait_info) 
    (SleepWakeup_set_wake_reason t.(sleepwakeup) wr) t.(schedthread).

Definition set_wake_reason_none t := set_wake_reason t NONE.

Definition get_wake_reason t := t.(sleepwakeup).(wake_reason).

Definition get_unique_id t := t.(unique_id).

(*TODO: sleep*)

(*TODO: counted_sleep*)

(*TODO: counted_sleep_delay*)

(*TODO: exit*)

(*TODO: self*)

Definition set_sleep_reason t sr := 
  mkThread t.(unique_id) t.(timer_id) t.(state) t.(wait_info) 
    (SleepWakeup_set_sleep_reason t.(sleepwakeup) sr) t.(schedthread).

Definition set_sleep_reason_wait t := set_sleep_reason t WAIT.

(*TODO: set_timer*)

(*TODO: clear_timer*)


Definition timeslice_reset t := 
  set_schedthread t (SchedThread.timeslice_reset t.(schedthread)).

Definition addthread t := set_schedthread t (SchedThread.addthread t.(schedthread)).

(********************************************************)
(*The double linked cycled list of thread*)

Module Thread_Obj <: DNode.

  Definition Obj := Thread.

  Definition eq_Obj (x y : Thread) :=
    beq_nat x.(unique_id) y.(unique_id).

  Definition A := nat.
  
  Definition test_Obj t n := beq_nat t.(unique_id) n.  

End Thread_Obj.

Module TO := CList Thread_Obj.

Definition RunQueue := TO.CList Thread.

Definition RunQueue_cstr := @nil Thread.

Definition get_thread (q : RunQueue) (tid : nat) : option (nat*nat).
induction q as [ |t q' IHq']; [exact None| ].
  case_eq (beq_nat tid t.(unique_id)); intros h.
    exact (Some ((get_priority t), 0)).  
    destruct IHq' as [x| ]. 
      destruct x as [f s]. exact (Some (f, (S s))).
      exact None. 
Defined.

Definition get_thread_t (q : RunQueue) (tid : nat) : option Thread :=
TO.get_Obj q tid.

Definition update_thread (q : RunQueue) (t : Thread) : RunQueue:=
TO.update_Obj q t.

(*should be next != this*)
Definition in_list (t : Thread) : bool := true.