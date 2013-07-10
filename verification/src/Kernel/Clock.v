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

Definition set_resolution (c : Clock)(r : Resolution) : Clock := mkclk (counter c) r.

Definition get_resolution (c : Clock) : Resolution := resolution c.


(**************************************************************)
(*The list of all clocks, including the real_time_clock*)

Module Clock_obj <: DNode.
  
  Definition Obj := Clock.

  Definition eq_Obj (x y : Clock) :=
    beq_nat x.(counter).(unique_counter_id) y.(counter).(unique_counter_id).

End Clock_obj.


Module CL := CList Clock_obj.

Definition ClockList := CL.CList Clock.
