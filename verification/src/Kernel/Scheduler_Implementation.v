Set Implicit Arguments.

Require Import BitArray.
Require Import Array.
Require Import QueueArray.

Require Import Scheduler_Base.
Require Import Thread.

Require Import Constant.

Require Import NPeano.

Definition QueueMap := array bool PRIORITIES.
Definition RunQueueArray := array RunQueue PRIORITIES.

Record Scheduler_Implementation := mkSI{

  scheduler_base : Scheduler_Base;
  
  queue_map : QueueMap;

  run_queue_array : RunQueueArray;

  timeslice_count : nat

}.

Definition set_scheduler_base si sb := 
  mkSI sb si.(queue_map) si.(run_queue_array) si.(timeslice_count).

Definition get_current_thread si := 
  array_get_thread_t si.(run_queue_array) (Scheduler_Base.get_current_thread si.(scheduler_base)).

Definition set_current_thread si tid := 
  set_scheduler_base si (Scheduler_Base.set_current_thread si.(scheduler_base) tid).

Definition set_need_reschedule si := 
  set_scheduler_base si (Scheduler_Base.set_need_reschedule si.(scheduler_base)).

Definition set_need_reschedule_t (si : Scheduler_Implementation) (t : Thread) : Scheduler_Implementation.
set (current := get_current_thread si).
destruct current as [current_t| ]; [ |exact si].
case_eq (ltb (get_priority t) (get_priority current_t)); intros h1.
  exact (set_need_reschedule si).
  
  destruct (get_state t) as [ | | | | | ]; [exact (set_need_reschedule si)| | | | |]; exact si.
Defined.

Definition get_need_reschedule si := Scheduler_Base.get_need_reschedule si.(scheduler_base).

Definition get_sched_lock si := Scheduler_Base.get_sched_lock si.(scheduler_base).

Definition clear_need_reschedule si := 
  set_scheduler_base si (Scheduler_Base.clear_need_reschedule si.(scheduler_base)).

Definition get_thread_switches si := Scheduler_Base.get_thread_switches si.(scheduler_base).

Definition set_thread_switches si n := 
  set_scheduler_base si (Scheduler_Base.set_thread_switches si.(scheduler_base) n).

Definition get_timeslice_count si := si.(timeslice_count).

Definition set_timeslice_count si count := 
  mkSI si.(scheduler_base) si.(queue_map) si.(run_queue_array) count.

Definition set_run_queue si index q := 
  mkSI si.(scheduler_base) si.(queue_map) (set_q si.(run_queue_array) index q) si.(timeslice_count).

(*TODO: set_idle_thread*)

Definition timeslice_cpu (si : Scheduler_Implementation) : Scheduler_Implementation.
destruct si.(timeslice_count) as [|]; [|exact si].
destruct (get_current_thread si) as [t| ]; [|exact si].
destruct (get_state t) as [ | | | | | ]; [ |exact si|exact si|exact si|exact si|exact si].
  set (index := get_priority t).
  set (q := nth_q si.(run_queue_array) index).
  set (q' := TO.rotate q).
  set (run_queue_array' := set_q si.(run_queue_array) index q').
  assert (sh : Scheduler_Base).
    destruct (TO.get_head q') as [o|]; [|exact si.(scheduler_base)].
      case_eq (Thread_Obj.eq_Obj o t); intros h. 
        exact si.(scheduler_base).
        exact (Scheduler_Base.set_need_reschedule si.(scheduler_base)).
  exact (mkSI sh si.(queue_map) run_queue_array' CYGNUM_KERNEL_SCHED_TIMESLICE_TICKS).
Defined.

Definition timeslice (si : Scheduler_Implementation) : Scheduler_Implementation.
destruct si.(timeslice_count) as [|n]; [exact si|].
  set (si' := set_timeslice_count si n).
  destruct n as [ | ]; [|exact si'].
    exact (timeslice_cpu si').
Defined.

Definition Scheduler_Implementation_cstr := 
  set_need_reschedule (mkSI (Scheduler_Base_cstr) (init_0 PRIORITIES) 
       (init PRIORITIES nil) CYGNUM_KERNEL_SCHED_TIMESLICE_TICKS).

Definition schedule si := 
  TO.get_head (nth_q si.(run_queue_array) (lsb si.(queue_map))).  

Definition add_thread (si : Scheduler_Implementation) (t: Thread) : Scheduler_Implementation.
set (t' := addthread (timeslice_reset t)).
set (index := get_priority t').
(*construct the updated queue_map*)
assert (queue_map' : QueueMap). 
 case_eq (TO.empty (nth_q si.(run_queue_array) index)); intros h.
    exact (set_1 si.(queue_map) index).
    exact si.(queue_map).
(*construct the update run_queue_array_array*)
assert (run_queue_array' : RunQueueArray).
  set (array_step1 := remove_t si.(run_queue_array) t').
  set (queue := nth_q array_step1 index).
  set (new_queue := TO.add_tail queue t').
  exact (set_q array_step1 index new_queue).
(*construct the result*)
exact (mkSI si.(scheduler_base) queue_map' run_queue_array' si.(timeslice_count)).
Defined.

Definition rem_thread (si : Scheduler_Implementation) (t : Thread) : Scheduler_Implementation.
set (index := get_priority t).  
assert (run_queue_array' : RunQueueArray).
  exact (remove_t si.(run_queue_array) t).
assert (queue_map' : QueueMap).
  case_eq (TO.empty (nth_q run_queue_array' index)); intros h.
    exact (set_0 si.(queue_map) index).
    exact si.(queue_map).
exact (mkSI si.(scheduler_base) queue_map' run_queue_array' si.(timeslice_count)).
Defined.

Definition unique (si : Scheduler_Implementation) := true.

Definition inc_sched_lock si := 
  set_scheduler_base si (Scheduler_Base.inc_sched_lock si.(scheduler_base)).

Definition zero_sched_lock si := 
  set_scheduler_base si (Scheduler_Base.zero_sched_lock si.(scheduler_base)).

Definition set_sched_lock si n := 
  set_scheduler_base si (Scheduler_Base.set_sched_lock si.(scheduler_base) n).

(*Step 1: find the thread in si; 
  Step 2: replace it with new thread which saved the timeslice_count
  I miss pointers...F**K!!!!!
*)
Definition timeslice_save (si : Scheduler_Implementation) (t : Thread) : Scheduler_Implementation.
set (t' := (Thread.timeslice_save t si.(timeslice_count))).
  set (index := get_priority t).
  set (new_queue := TO.add_tail (TO.remove (nth_q si.(run_queue_array) index) t) t').
  exact (mkSI si.(scheduler_base) si.(queue_map) 
              (set_q si.(run_queue_array) index new_queue) si.(timeslice_count)).
Defined.

Definition timeslice_restore si t := set_timeslice_count si (Thread.get_timeslice_count t).


