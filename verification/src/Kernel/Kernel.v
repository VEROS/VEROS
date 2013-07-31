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

  cl : ClockList;

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
  match (Scheduler.get_thread k.(sh) tt.(thread_id)) with
    |Some t => update_thread k (Thread.set_threadtimer t tt)
    |None => k
  end.   

Definition update_clock k c :=
  mkK k.(sh) k.(lq) (Clock.update_clock k.(cl) c) k.(next_unique_id).

Definition lock k := set_scheduler k (Scheduler.lock k.(sh)).

Definition unlock k := set_scheduler k (Scheduler.unlock k.(sh)).

(*------------------------------clock------------------------------------*)

Definition synchronize (k : Kernel)(tt : ThreadTimer) : (Kernel * ThreadTimer).
destruct (get_clock k.(cl) (get_counter_id tt)) as [c|]; [|exact (k, tt)].
  set (interval := get_interval tt).
  destruct interval as [ | ]; [exact (k, tt)|].
    set (d := (current_value c) + interval - (get_trigger tt)).
      case (ltb interval d).
        set(tt' := set_trigger tt (interval * (d-1)/interval)).
        exact ((update_threadtimer k tt'), tt').

        exact (k, tt).
Defined.

Definition add_alarm (k : Kernel)(tt : ThreadTimer) : Kernel.
destruct (get_clock k.(cl) (get_counter_id tt)) as [c|]; [|exact k].
  set (tt' := set_enable tt true).
  set (c' := set_threadtimer_list c (IL.add_tail (get_threadtimer_list c) (get_timer_id tt))).
  case (leb (get_trigger tt') (current_value c)).
  (*TO_DO: alarm->alarm(alarm, alarm->data)*)
    case ((negb (beq_nat (get_interval tt') 0)) && (get_enable tt')). 
      set (tt'' := set_trigger tt' ((get_trigger tt') + (get_interval tt'))).
      exact (update_clock (fst (synchronize k tt'')) c').
     
      exact (update_threadtimer k (set_enable tt' false)).
  exact (update_clock (update_threadtimer k tt') c').
Defined.

Definition enable (k : Kernel)(tt : ThreadTimer) : Kernel.
destruct (get_clock k.(cl) (get_counter_id tt)) as [c|]; [|exact k].
set (k' := lock k). assert (k'' : Kernel).
case (get_enable tt). 
  exact k'.

  destruct (synchronize k tt) as [ker tt']. exact (add_alarm ker tt').
exact (unlock k'').
Defined.

Definition rem_alarm (k : Kernel)(tt : ThreadTimer) : Kernel.
destruct (get_clock k.(cl) (get_counter_id tt)) as [c|]; [|exact k].
  set (c':= set_threadtimer_list c (IL.remove (get_threadtimer_list c) (get_timer_id tt))).
  exact (update_clock (update_threadtimer k (set_enable tt false)) c').
Defined.

Definition disable (k : Kernel)(tt : ThreadTimer) : Kernel.
destruct (get_clock k.(cl) (get_counter_id tt)) as [c|]; [|exact k].
set (k' := lock k). assert (k'' : Kernel).
case (get_enable tt). 
  exact (rem_alarm k' tt). 
  exact k'.
exact (unlock k'').
Defined.

Definition initialize (k : Kernel)(tt : ThreadTimer)(t i : nat) : Kernel.
destruct (get_clock k.(cl) (get_counter_id tt)) as [c|]; [|exact k].
set (k' := lock k). assert (k'' : Kernel).
case (get_enable tt). 
  exact (rem_alarm k' tt).
  exact k'.
set (tt' := (set_interval (set_trigger tt t) i)).
exact (unlock (add_alarm (update_threadtimer k'' tt') tt')).
Defined.

(*TODO: tick*)
(*
Definition tick (k : Kernel)(c : Clock)(ticks : nat) : Kernel.
destruct (CL.inside k.(cl) c) as [ | ]; [|exact k].
  induction ticks as [|n IHn]; [exact k|].
*)    

(*-------------------------- end of clock ------------------------------*)

(*----------------------- Scheduler & Thread ---------------------------*)

Definition remove (k : Kernel)(t : Thread) : Kernel * Thread.
set (t' := set_current_queue t NULL).
set (k' := update_thread k t').
destruct (get_current_queue t) as [n|n| ]; [ | |exact (k, t)].
  (*Mutex : we don't consider mutex yet*)
  exact (k', t').

  (*Semaphore : we don't consider semaphore yet*)
  exact (k', t'). 
Defined.

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

Definition resume (k : Kernel)(t : Thread) : Kernel.
set(k' := lock k). assert (k'' : Kernel).
destruct (get_suspend_count t) as [|n]; [exact k'|].
  set(t' := set_suspend_count t n).  
  destruct n as [|n']; [|exact (update_thread k' t')].
    (*TODO: state &= ~SUSPENDED*)
    destruct (get_state t') as [ | | | | | ]; [exact (add_thread k' t')| | | | | ]; exact k'.
exact (unlock k'').
Defined.

Definition set_idle_thread (k : Kernel)(t : Thread) : Kernel :=
resume (set_current_thread k t.(unique_id)) t.

Definition to_queue_head (k : Kernel)(t : Thread) : Kernel.
set (k' := lock k). assert (k'' : Kernel).
destruct (get_current_queue t) as [n|n| ]; [exact k'|exact k'| ].
destruct (in_list t) as [ | ]; [|exact (unlock k')].
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