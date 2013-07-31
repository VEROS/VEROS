Set Implicit Arguments.

Require Import Scheduler_Implementation.
Require Import Thread.
Require Import NPeano.

Require Import QueueArray.

Record Scheduler := mkS {
  sched_imp : Scheduler_Implementation
}.

Definition get_queue_map s := Scheduler_Implementation.get_queue_map s.(sched_imp).

Definition set_queue_map s qm := mkS (Scheduler_Implementation.set_queue_map s.(sched_imp) qm).

Definition get_timeslice_count s := Scheduler_Implementation.get_timeslice_count s.(sched_imp).

Definition set_timeslice_count s n := mkS (Scheduler_Implementation.set_timeslice_count s.(sched_imp) n).

Definition lock s := mkS (Scheduler_Implementation.inc_sched_lock s.(sched_imp)).

Definition get_current_thread s := Scheduler_Implementation.get_current_thread s.(sched_imp).

Definition set_current_thread s tid := mkS (Scheduler_Implementation.set_current_thread s.(sched_imp) tid).

Definition get_need_reschedule s := Scheduler_Implementation.get_need_reschedule s.(sched_imp).

Definition set_need_reschedule s := mkS (Scheduler_Implementation.set_need_reschedule s.(sched_imp)).

Definition set_need_reschedule_t s t := mkS (Scheduler_Implementation.set_need_reschedule_t s.(sched_imp) t).

Definition get_run_queue s priority : ThreadQueue := nth_q s.(sched_imp).(run_queue_array) priority.

Definition set_run_queue s index q := 
  mkS (Scheduler_Implementation.set_run_queue s.(sched_imp) index q).

Definition schedule s := Scheduler_Implementation.schedule s.(sched_imp).

Definition set_sched_lock s n := mkS (Scheduler_Implementation.set_sched_lock s.(sched_imp) n).

Definition zero_sched_lock s := mkS (Scheduler_Implementation.zero_sched_lock s.(sched_imp)).

Definition get_sched_lock s:= Scheduler_Implementation.get_sched_lock s.(sched_imp).

Definition clear_need_reschedule s := mkS (Scheduler_Implementation.clear_need_reschedule s.(sched_imp)).

Definition timeslice_save s t := mkS (Scheduler_Implementation.timeslice_save s.(sched_imp) t).

Definition timeslice_restore s t := mkS (Scheduler_Implementation.timeslice_restore s.(sched_imp) t).

Definition get_thread_switches s := Scheduler_Implementation.get_thread_switches s.(sched_imp).

Definition set_thread_switches s n := mkS (Scheduler_Implementation.set_thread_switches s.(sched_imp) n).

Definition update_thread s t := mkS (Scheduler_Implementation.update_thread s.(sched_imp) t).

Definition get_thread s t := Scheduler_Implementation.get_thread s.(sched_imp) t.

Definition unlock_inner (s: Scheduler) (new_lock : nat) : Scheduler.
(*if new_lock == 0 and there is any DSR pended, call all the DSRs*)
destruct (get_current_thread s) as [current|]; [|exact s]. 
assert (s' : Scheduler). destruct (get_need_reschedule s) as [ | ]; [ |exact s].
  assert (s'' : Scheduler). destruct (schedule s) as [next|]; [ |exact s].
    destruct (Thread_Obj.eq_Obj current next) as [ | ]; [exact s| ].
      set (s_tmp1 := set_thread_switches s (S (get_thread_switches s))).
      set (s_tmp2 := timeslice_save s_tmp1 current).
      (*HAL_THREAD_SWITCH_CONTEXT( &current->stack_ptr, &next->stack_ptr );*)
      set (s_tmp3 := set_current_thread s_tmp2 current.(unique_id)).
      exact (timeslice_restore s_tmp3 current).
  destruct (get_state current) as [ | | | | | ]; [exact s| | | | | ]; exact (clear_need_reschedule s'').
destruct new_lock as [ | ].
  exact (zero_sched_lock s'). (*if( Cyg_Interrupt::DSRs_pending() ) {
                                  inc_sched_lock();   // reclaim the lock
                                  continue;           // go back to head of loop
                                }*)
  exact (set_sched_lock s' new_lock).
Defined.

Definition unlock s := 
match (get_sched_lock s) with
|O => s (*shouldn't be*)
|S n => match n with
        |O => unlock_inner s O
        |S _ => set_sched_lock s n
        end
end.

Definition reschedule s:= unlock_inner s (get_sched_lock s).

Definition unlock_reschedule s :=
match (get_sched_lock s) with
|O => s (*shouldn't be*)
|S n => unlock_inner s n
end.

Definition unlock_simple s := 
  if (ltb 1 (get_sched_lock s)) 
  then set_sched_lock s ((get_sched_lock s) - 1)
  else zero_sched_lock s.

Definition start_cpu s := 
match (schedule s) with
|Some next => set_current_thread (clear_need_reschedule s) next.(unique_id) (*HAL_THREAD_LOAD_CONTEXT*)
|None => s (*shouldn't be*)
end.

Definition start s := start_cpu s.

Definition thread_entry (s : Scheduler) (t : Thread) : Scheduler.
set (s' := timeslice_restore (set_current_thread (clear_need_reschedule s) 
                              t.(unique_id)) (timeslice_reset t)). 
destruct (get_sched_lock s') as [ |n].
  exact s'.
  exact (set_sched_lock (unlock_inner (set_sched_lock s' 1) O) O).
Defined.

Definition rotate_queue (s : Scheduler)(priority : nat) : Scheduler.
set (s' := lock s). set(queue := nth_q s'.(sched_imp).(run_queue_array) priority).
destruct (TO.empty queue) as [ | ]; [exact (unlock s')| ].
  exact (unlock (set_need_reschedule (set_run_queue s' priority (TO.rotate queue)))).
Defined.    

Definition yield (s : Scheduler) (t : Thread) : Scheduler.
set (s' := lock s). assert (s'' : Scheduler).
destruct (get_state t) as [ | | | | | ]; [ |exact s'|exact s'|exact s'|exact s'|exact s'].
  set (index := get_priority t).
  set (queue := TO.rotate (nth_q s'.(sched_imp).(run_queue_array) index)).
  destruct (TO.get_head queue) as [head| ]; [ |exact (set_run_queue s' index queue)].
    destruct (Thread_Obj.eq_Obj head t) as [ | ]. 
      exact (set_run_queue s' index (TO.add_head (TO.remove queue head) (timeslice_reset head))).
      exact (set_need_reschedule (set_run_queue s' index queue)).
exact (unlock_reschedule s'').
Defined.