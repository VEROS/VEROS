Set Implicit Arguments.

Require Import Bool.
Require Import NPeano.
Require Import EqNat.
Require Import Clock.
Require Import ThreadTimer.
Require Import Thread.
Require Import Scheduler_Implementation.
Require Import Scheduler.
Require Import SuspendQueue.

Record Kernel := mkK {
  sh : Scheduler;

  lq : ThreadQueue; (*All the lonely threads that are not in any queue at all*)

  cl : Clock; (*realtime_clock*)

  next_unique_id : nat
}.

Definition inc_next_unique_id k := mkK k.(sh) k.(lq) k.(cl) (S k.(next_unique_id)).

Definition get_queue_map k := Scheduler.get_queue_map k.(sh).

Definition set_queue_map k qm :=
  mkK (Scheduler.set_queue_map k.(sh) qm) k.(lq) k.(cl) k.(next_unique_id).

Definition set_scheduler k sh := mkK sh k.(lq) k.(cl) k.(next_unique_id). 

Definition get_run_queue k index := Scheduler.get_run_queue k.(sh) index.

Definition set_run_queue k index q := set_scheduler k (Scheduler.set_run_queue k.(sh) index q).

Definition set_need_reschedule k := set_scheduler k (Scheduler.set_need_reschedule k.(sh)).

Definition set_need_reschedule_t k t := set_scheduler k (Scheduler.set_need_reschedule_t k.(sh) t).

Definition get_current_thread k := Scheduler.get_current_thread k.(sh).

Definition set_current_thread k tid := set_scheduler k (Scheduler.set_current_thread k.(sh) tid).

Definition get_timeslice_count k := Scheduler.get_timeslice_count k.(sh).

Definition set_timeslice_count k n := 
  set_scheduler k (Scheduler.set_timeslice_count k.(sh) n).

Definition set_lonely_queue k q := mkK k.(sh) q k.(cl) k.(next_unique_id).

Definition add_lonely_thread k t := set_lonely_queue k (TO.add_tail k.(lq) t).

Definition rem_lonely_thread k t := set_lonely_queue k (TO.remove k.(lq) t).

Definition get_thread k tid :=
  match (TO.get_Obj k.(lq) tid) with
    |Some t => Some t
    |None => match Scheduler.get_thread k.(sh) tid with
               |Some t => Some t
               |None => None
             end
  end.

(*try to update the thread in runqueue or lonely queue, since we don't know where it is*)
Definition update_thread k t := 
  set_lonely_queue (set_scheduler k (Scheduler.update_thread k.(sh) t)) (Thread.update_thread k.(lq) t).

Definition replace_thread (k : Kernel)(t t' : Thread) : Kernel.
(*Mutex : not considered*)
(*Semaphore : not considered, either!*)
case (TO.inside k.(lq) t).
  exact (set_lonely_queue k (Thread.replace_thread k.(lq) t t')).
  exact (set_scheduler k (Scheduler.replace_thread k.(sh) t t')).
Defined.    

Definition update_threadtimer k tt := 
  match (get_thread k tt.(thread_id)) with
    |Some t => update_thread k (Thread.set_threadtimer t tt)
    |None => k
  end.   

(*No customized clock considered yet*)
Definition get_clock k (cid : nat) := k.(cl).

Definition set_clock k c :=
  mkK k.(sh) k.(lq) c k.(next_unique_id).

(*No customized clocks considered yet*)
Definition update_clock (k : Kernel)(c : Clock) :=
set_clock k c. 

Definition lock k := set_scheduler k (Scheduler.lock k.(sh)).

Definition unlock k := set_scheduler k (Scheduler.unlock k.(sh)).

(*------------------------------clock------------------------------------*)

Definition synchronize (k : Kernel)(tt : ThreadTimer) : (Kernel * ThreadTimer).
set(c := get_clock k (get_counter_id tt)).
set (interval := get_interval tt).
destruct interval as [ | ]; [exact (k, tt)|].
set (d := (current_value c) + interval - (get_trigger tt)).
case (ltb interval d).
  -set(tt' := set_trigger tt (interval * (d-1)/interval)).
   exact ((update_threadtimer k tt'), tt').
  -exact (k, tt).
Defined.

Definition add_alarm (k : Kernel)(tt : ThreadTimer) : Kernel.
set(c := get_clock k (get_counter_id tt)).
set (tt' := set_enable tt true).
set (c' := set_threadtimer_list c (IL.add_tail (get_threadtimer_list c) (get_timer_id tt))).
case (leb (get_trigger tt') (current_value c)).
(*TODO: alarm->alarm(alarm, alarm->data)*)
  -case ((negb (beq_nat (get_interval tt') 0)) && (get_enable tt')). 
    +set (tt'' := set_trigger tt' ((get_trigger tt') + (get_interval tt'))).
     exact (update_clock (fst (synchronize k tt'')) c').     
    +exact (update_threadtimer k (set_enable tt' false)).
  -exact (update_clock (update_threadtimer k tt') c').
Defined.

Definition enable (k : Kernel)(tt : ThreadTimer) : Kernel.
set(c := get_clock k (get_counter_id tt)).
set (k' := lock k). assert (k'' : Kernel).
-case (get_enable tt). 
  +exact k'.
  +destruct (synchronize k tt) as [ker tt']. exact (add_alarm ker tt').
-exact (unlock k'').
Defined.

Definition rem_alarm (k : Kernel)(tt : ThreadTimer) : Kernel.
set(c := get_clock k (get_counter_id tt)).
set (c':= set_threadtimer_list c (IL.remove (get_threadtimer_list c) (get_timer_id tt))).
exact (update_clock (update_threadtimer k (set_enable tt false)) c').
Defined.

Definition disable (k : Kernel)(tt : ThreadTimer) : Kernel.
set(c := get_clock k (get_counter_id tt)).
set (k' := lock k). assert (k'' : Kernel).
-case (get_enable tt). 
  +exact (rem_alarm k' tt). 
  +exact k'.
-exact (unlock k'').
Defined.

Definition initialize (k : Kernel)(tt : ThreadTimer)(t i : nat) : Kernel.
set(c := get_clock k (get_counter_id tt)).
set (k' := lock k). assert (k'' : Kernel).
-case (get_enable tt). 
  +exact (rem_alarm k' tt).
  +exact k'.
-set (tt' := (set_interval (set_trigger tt t) i)).
 exact (unlock (add_alarm (update_threadtimer k'' tt') tt')).
Defined.

Definition get_threadtimer_by_id (k : Kernel)(ttid : nat) : option ThreadTimer.
destruct (Thread.get_threadtimer_by_id k.(lq) ttid) as [tt|]; [exact (Some tt)|].
(*Mutex*)(*Semaphore*)
exact (Scheduler.get_threadtimer_by_id k.(sh) ttid).
Defined.

Definition tick_aux (k : Kernel)(counter : nat)(ttl : IDList) : nat.
induction ttl as [|ttid ttl' IHl'].
-exact 1.
-destruct (get_threadtimer_by_id k ttid) as [tt|]; [ |exact IHl'].
 exact (max ((counter - (get_trigger tt)) / (get_interval tt)) IHl').
Defined. 

Definition one_scan (k : Kernel)(c : Clock) : Kernel. 
set (ttl := get_threadtimer_list c).
induction ttl as [|ttid ttl' IHl']; [exact k|].
destruct (get_threadtimer_by_id k ttid) as [tt|]; [|exact k].
destruct (leb (get_trigger tt) (current_value c)).
-set (c' := set_threadtimer_list c (IL.remove (get_threadtimer_list c) ttid)).
 set (k' := update_clock k c').
 assert (tmp : Kernel).
 +destruct (get_interval tt).
   *exact (update_threadtimer k' (set_enable tt false)).
   *set (tt' := set_trigger tt ((get_trigger tt) + (get_interval tt))).
    exact (add_alarm (update_threadtimer k' tt') tt'). 
 (*TODO : alarm->alarm(alarm, alarm->data*)
 +exact tmp.
-exact IHl'.
Defined.

Definition tick (k : Kernel)(c : Clock)(ticks : nat) : Kernel.
induction ticks as [|n IHn]; [exact k|].
set (c' := inc_clock c). set (k' := update_clock (lock IHn) c').
set (scan_count := tick_aux k' (current_value c') (get_threadtimer_list c')).
assert (tk : Kernel).
induction scan_count as [|m IHm]; [exact k'| ].
exact (one_scan IHm (get_clock IHm (get_clock_id c'))).
exact (unlock tk).
Defined.

(*-------------------------- end of clock ------------------------------*)

(*----------------------- Scheduler & Thread ---------------------------*)

Definition in_list (k : Kernel)(t : Thread) : bool.
destruct (get_current_queue t) as [n|n|].
  exact false. (*Mutex : we don't consider mutex yet*)
  exact false. (*Semaphore : we don't consider semaphore yet*)
  case (thread_check_state t RUNNING).
    destruct (get_run_queue k (get_priority t)) as [|t' l].
      exact false. (*shouldn't be*)
      destruct l as [|t'' l']. 
        exact false. (*only one thread in the run queue, shoule be t*)
        exact true.
    exact false. (*in the lonely queue, not in list actually*)
Defined.

Definition reschedule k := set_scheduler k (Scheduler.reschedule k.(sh)).

Definition remove (k : Kernel)(t : Thread) : Kernel * Thread.
set (t' := set_current_queue t NULL).
set (k' := rem_lonely_thread k t'). (*remove it frome the lonely queue, just to preserve one copy*)
destruct (get_current_queue t) as [n|n| ]; [ | |exact (k, t)].
  (*Mutex : we don't consider mutex yet*)
  exact (k', t').

  (*Semaphore : we don't consider semaphore yet*)
  exact (k', t'). 
Defined.

Definition enqueue (k : Kernel)(t : Thread) : Kernel :=
  match (get_current_queue t) with
    |mutex n => k  (*Mutex : we don't consider mutex yet*)
    |semaphore n => k  (*Semaphore : we don't consider semaphore yet*)
    |NULL => k (*shouldn't be*)
  end.

Definition add_thread (k : Kernel) (t: Thread) : Kernel.
set (index := get_priority t). destruct (remove k t) as [k' t'].
set (queue := get_run_queue k' index).
assert (queue_map' : QueueMap). 
 case_eq (TO.empty queue); intros h. 
    exact (BitArray.set_1 (get_queue_map k') index).
    exact (get_queue_map k').
set (k'' := set_run_queue (set_queue_map k' queue_map') index (TO.add_tail queue t')).
exact (update_thread (set_need_reschedule_t k'' t') (timeslice_reset t')).
Defined.

Definition rem_thread k t := add_lonely_thread (set_scheduler k (Scheduler.rem_thread k.(sh) t)) t.

Definition resume (k : Kernel)(t : Thread) : Kernel.
set(k' := lock k). assert (k'' : Kernel).
destruct (get_suspend_count t) as [|n]; [exact k'|].
  set(t' := set_suspend_count t n).  
  destruct n as [|n']; [|exact (update_thread k' t')].
    set (t'' := thread_alter_state t' SUSPENDED false). 
    destruct (thread_check_state_eq t'' RUNNING). 
      exact (add_thread k' t''). 
      exact (update_thread k' t'').
exact (unlock k'').
Defined.

Definition set_idle_thread (k : Kernel)(t : Thread) : Kernel :=
resume (set_current_thread k t.(unique_id)) t.

Definition to_queue_head (k : Kernel)(t : Thread) : Kernel.
set (k' := lock k). assert (k'' : Kernel).
destruct (get_current_queue t) as [n|n| ]; [exact k'|exact k'| ].
destruct (in_list k' t) as [ | ]; [|exact (unlock k')].
  set (index := get_priority t). 
  set (queue := TO.to_head (get_run_queue k' index) t).
  exact (set_need_reschedule_t (set_run_queue k' index queue) t).
exact (unlock k'').
Defined.

Definition reinitialize (k : Kernel)(t : Thread) : Kernel.
set (k' := disable k (get_threadtimer t)).
destruct (get_thread  k' t.(unique_id)) as [t'| ]; [|exact k'].
  exact (inc_next_unique_id (replace_thread k' t (Thread.reinitialize_thread t' k'.(next_unique_id)))).  
Defined.

Definition wake (k : Kernel)(t : Thread) : Kernel.
set (k' := lock k). assert (k'' : Kernel).
destruct (thread_check_state t SLEEPSET) as [ | ]; [ |exact k'].
  set (t' := thread_alter_state t SLEEPSET false).
  destruct (remove k' t') as [kr tr].
  case (thread_check_state_eq tr RUNNING).
    exact (add_thread kr tr).
    exact kr.
exact (unlock k'').
Defined.

Definition counted_wake (k : Kernel)(t : Thread) : Kernel.
set (k' := lock k). assert (k'' : Kernel).
case (thread_check_state t COUNTSLEEP).
  exact (wake k' (set_wake_reason (set_sleep_reason t NONE) DONE)).
  exact (update_thread k' (set_wakeup_count t (S (get_wakeup_count t)))).
exact (unlock k'').
Defined.

Definition cancel_counted_wake k t := unlock (update_thread (lock k) (set_wakeup_count t 0)).

Definition suspend (k : Kernel)(t : Thread) : Kernel.
set (t' := set_suspend_count t (S (get_suspend_count t))).
set (k' := update_thread (lock k) t'). assert (k'' : Kernel).
case (thread_check_state_eq t RUNNING).
  exact (rem_thread k' t').
  exact k'.
exact (unlock (update_thread k'' (thread_alter_state t' SUSPENDED true))). 
Defined.

(*to help the definition of release*)
Definition check_sleep_reason r := 
  match r with
    |NONE => true
    |DESTRUCT => true
    |BREAK => true
    |EXIT => true
    |DONE => true
    |WAIT => false
    |TIMEOUT => false
    |DELAY => false
  end.

Definition release (k : Kernel)(t : Thread) : Kernel.
set (k' := lock k).
case (check_sleep_reason (get_sleep_reason t)).
  exact (unlock k').
  
  set (t' := set_wake_reason (set_sleep_reason t NONE) BREAK).
  exact (unlock (wake (update_thread k' t') t')).
Defined.

Definition self (k : Kernel) : option Thread := get_current_thread k.

Definition clear_timer (k : Kernel) := 
  match (self k) with
    |Some t => disable k (get_threadtimer t)
    |None => k (*shouldn't be*)
  end.

Definition exit (k : Kernel) : Kernel.
set (k' := clear_timer (lock k)). assert (k'' : Kernel). 
destruct (self k') as [t|]; [|exact k'].
  case (thread_check_state_eq t EXITED).
    exact k'.

    set (t' := thread_alter_state_eq t EXITED).
    exact (rem_thread (update_thread k' t') t').
exact (reschedule k'').
Defined.

Definition force_resume (k : Kernel) (t : Thread) : Kernel.
set (k' := lock k). assert (k'' : Kernel).
case (ltb 0 (get_suspend_count t)).
  set (t' := thread_alter_state (set_suspend_count t 0) SUSPENDED false).
  case (thread_check_state_eq t' RUNNING).
    exact (add_thread k' t').
    exact (update_thread k' t').

  exact k'.
exact (unlock k'').
Defined.

Definition kill (k : Kernel) (t : Thread) : Kernel.
destruct (get_current_thread k) as [current|]; [|exact k].
case (Thread_Obj.eq_Obj t current).
  exact (exit k).
  
  set (k' := force_resume (lock k) t).
  destruct (get_thread k' (get_unique_id t)) as [t'|]; [|exact k].
    set (k'' := disable k' (get_threadtimer t')).
    destruct (get_thread k'' (get_unique_id t)) as [t''|]; [|exact k].
      case (reason_eq (get_wake_reason t'') EXIT).
        exact (unlock (wake k'' t'')).
        
        case_eq (get_sleep_reason t''); intros h.
          assert (k_NONE : Kernel).
          case (thread_check_state_eq t'' RUNNING).
            exact (rem_thread k'' t'').
            exact k''.
          set(t_NONE := thread_alter_state_eq t'' EXITED).
          exact (unlock (wake (update_thread k_NONE t_NONE) t_NONE)). 
          
          set (t_WTD := set_wake_reason (set_sleep_reason t'' NONE) EXIT).
          exact (unlock (wake (update_thread k'' t_WTD) t_WTD)).
          
          set (t_WTD := set_wake_reason (set_sleep_reason t'' NONE) EXIT).
          exact (unlock (wake (update_thread k'' t_WTD) t_WTD)).

          set (t_WTD := set_wake_reason (set_sleep_reason t'' NONE) EXIT).
          exact (unlock (wake (update_thread k'' t_WTD) t_WTD)).

          exact (unlock k'').          

          exact (unlock k'').          

          exact (unlock k'').

          exact (unlock k'').
Defined.

Definition sleep (k : Kernel) : Kernel.
destruct (get_current_thread k) as [current|]; [|exact k].
set (k' := lock k). assert (k'' : Kernel).
case (thread_check_state_eq current RUNNING).
  exact (rem_thread k' current).
  exact k'.
exact (unlock (update_thread k'' (thread_alter_state current SLEEPING true))).
Defined.

Definition set_timer (k : Kernel)(tr : nat)(sr : Reason) : Kernel.
destruct (self k) as [t|]; [|exact k].
set (t' := set_wake_reason (set_sleep_reason t sr) NONE). 
exact (initialize (update_thread k t') (get_threadtimer t') tr 0).
Defined.

Definition counted_sleep (k : Kernel) : Kernel.
destruct (get_current_thread k) as [current|]; [|exact k].
set (k' := lock k). assert (k'' : Kernel).
destruct (get_wakeup_count current) as [|n].
  set (t_0 := set_sleep_reason current WAIT).
  exact (update_thread (sleep (update_thread k' t_0)) (thread_alter_state t_0 COUNTSLEEP true)). 

  exact (update_thread k' (set_wakeup_count current n)).
set (k_unlock := unlock k'').
destruct (get_thread k_unlock (get_unique_id current)) as [t|]; [|exact k].
destruct (get_wake_reason t) as [ | | | | | | | ]; 
   [ | | | | |exact (exit k_unlock)|exact (exit k_unlock)| ]; exact k_unlock.
Defined.

Definition counted_sleep_delay (k : Kernel)(delay : nat) : Kernel. 
destruct (get_current_thread k) as [current|]; [|exact k].
set (k' := lock k). assert (k'' : Kernel).
-destruct (get_wakeup_count current) as [|n].
  +set(clock := k'.(cl)).
   set (k_0 := set_timer k' ((current_value clock) + delay) TIMEOUT).
   destruct (get_thread k_0 (get_unique_id current)) as [t|]; [|exact k].
   assert (k_NONE : Kernel).
    *case (reason_eq (get_wake_reason t) NONE).
      set (t_0 := set_sleep_reason t TIMEOUT).
      exact (clear_timer (reschedule (update_thread (sleep (update_thread k_0 t_0)) 
                                            (thread_alter_state t_0 COUNTSLEEP true)))). 
      exact k_0.
    *exact k_NONE.
  +exact (update_thread k' (set_wakeup_count current n)).
-set (k_unlock := unlock k'').
 destruct (get_thread k_unlock (get_unique_id current)) as [t|]; [|exact k].
 destruct (get_wake_reason t) as [ | | | | | | | ]; 
   [ | | | | |exact (exit k_unlock)|exact (exit k_unlock)| ]; exact k_unlock.
Defined.

Definition delay (k : Kernel)(t: Thread)(delay : nat) : Kernel.
set (k' := sleep (lock k)). 
set(clock := k'.(cl)).
set (k'' := clear_timer (unlock (set_timer k' ((current_value clock) + delay) DELAY))).
destruct (get_thread k'' (get_unique_id t)) as [t'|]; [|exact k].
destruct (get_wake_reason t') as [ | | | | | | | ]; 
   [ | | | | |exact (exit k'')|exact (exit k'')| ]; exact k''.
Defined.  

Definition set_priority (k : Kernel)(t : Thread)(pri : nat) : Kernel.
set (k_lock := lock k).

assert (k_remove : Kernel).
case (thread_check_state_eq t RUNNING).
  exact (rem_thread k_lock t).
  case (thread_check_state t SLEEPING).
    exact (fst (remove k_lock t)).
    exact k_lock.

set (t_pri := Thread.set_priority t pri).
set (k_pri := update_thread k_remove t_pri).
 
assert (k_add : Kernel).
case (thread_check_state_eq t_pri RUNNING).
  exact (add_thread k_pri t_pri).
  case (thread_check_state t SLEEPING).
    exact (enqueue k_pri t_pri).
    exact k_pri.

assert (k_res : Kernel).
destruct (get_current_thread k_add) as [current|]; [|exact k].
case (Thread_Obj.eq_Obj current t_pri).
  exact (set_need_reschedule k_add).
  exact (set_need_reschedule_t k_add t_pri).

exact (unlock k_res).
Defined.
