Set Implicit Arguments.

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


  