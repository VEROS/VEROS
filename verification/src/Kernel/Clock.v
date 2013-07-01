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


(*DO : Clock_cstr*)

(*DO : set_resolution*)

(*DO : get_resolution*)


  