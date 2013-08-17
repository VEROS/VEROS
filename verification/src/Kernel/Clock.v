Set Implicit Arguments.

Require Import EqNat.
Require Import DLClist.
Require Import Counter.
Require Import ThreadTimer.

Record Resolution := mkrl{

  dividend : nat;
  divisor : nat

}.


Record Clock := mkclk{

  counter : Counter;
  resolution : Resolution

}.

Definition Clock_cstr (c :  Counter)(r: Resolution) : Clock := mkclk c r.

Definition set_resolution (c : Clock)(r : Resolution) : Clock := mkclk c.(counter) r.

Definition get_resolution (c : Clock) : Resolution := resolution c.

Definition get_clock_id c := Counter.get_counter_id c.(counter).

Definition current_value c := Counter.current_value c.(counter).

Definition current_value_hi c := Counter.current_value_hi c.(counter).

Definition current_value_lo c := Counter.current_value_lo c.(counter). 

Definition get_threadtimer_list c := c.(counter).(threadtimer_list).

Definition set_counter cl c := mkclk c cl.(resolution).

Definition set_value c n := set_counter c (Counter.set_value c.(counter) n).

Definition set_threadtimer_list c l := set_counter c (Counter.set_threadtimer_list c.(counter) l).

Definition inc_clock cl := set_counter cl (Counter.inc_counter cl.(counter)). 

(**************************************************************)
(*The list of all clocks, including the real_time_clock*)

Module Clock_obj <: DNode.
  
  Definition Obj := Clock.

  Definition eq_Obj (x y : Clock) :=
    beq_nat x.(counter).(unique_counter_id) y.(counter).(unique_counter_id).
  
  Definition A := nat.
  
  Definition test_Obj x n := beq_nat x.(counter).(unique_counter_id) n.

End Clock_obj.

Module CL := CList Clock_obj.

Definition ClockList := CL.CList Clock.

Definition get_clock cl cid := CL.get_Obj cl cid.

Definition update_clock cl c :=  CL.update_Obj cl c.

Definition find_clock (cl : ClockList)(ttid : nat) : option Clock.
induction cl as [|c cl' IHcl']; [exact None|].
  case (IL.inside (get_threadtimer_list c) ttid).
    exact (Some c).
    exact IHcl'.
Defined.