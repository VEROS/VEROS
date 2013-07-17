Set Implicit Arguments.

Require Import EqNat.
Require Import DLClist.
Require Import Counter.

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

Definition get_clock_id c := get_counter_id c.(counter).

(*TO DO: Clock_add_alarm*)

Definition Clock_rem_alarm c a := mkclk (rem_alarm c.(counter) a) c.(resolution). 

Definition Clock_current_value c := current_value c.(counter).

Definition Clock_set_value c n := set_value c.(counter) n.

Definition Clock_current_value_hi c := current_value_hi c.(counter).

Definition Clock_current_value_lo c := current_value_lo c.(counter). 


(**************************************************************)
(*The list of all clocks, including the real_time_clock*)

Module Clock_obj <: DNode.
  
  Definition Obj := Clock.

  Definition eq_Obj (x y : Clock) :=
    beq_nat x.(counter).(unique_counter_id) y.(counter).(unique_counter_id).

End Clock_obj.


Module CL := CList Clock_obj.

Definition ClockList := CL.CList Clock.
