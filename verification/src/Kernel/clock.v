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


(**)
  