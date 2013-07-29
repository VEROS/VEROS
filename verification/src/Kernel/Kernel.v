Set Implicit Arguments.

Require Import Bool.
Require Import NPeano.
Require Import EqNat.
Require Import Clock.
Require Import ThreadTimer.
Require Import Scheduler.

Record Kernel := mkK {
  sh : Scheduler;
  cl : ClockList
}.

Definition set_scheduler k sh := mkK sh k.(cl). 

Definition get_timeslice_count k := Scheduler.get_timeslice_count k.(sh).

Definition set_timeslice_count k n := 
  set_scheduler k (Scheduler.set_timeslice_count k.(sh) n).

Definition update_thread k t := set_scheduler k (Scheduler.update_thread k.(sh) t).

Definition update_threadtimer k tt := 
  match (Scheduler.get_thread k.(sh) tt.(thread_id)) with
    |Some t => update_thread k (Thread.set_threadtimer t tt)
    |None => k
  end.   

Definition update_clock k c :=
  mkK k.(sh) (Clock.update_clock k.(cl) c).

Definition lock k := set_scheduler k (Scheduler.lock k.(sh)).

Definition unlock k := set_scheduler k (Scheduler.unlock k.(sh)).

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