Require Import Bool.
Require Import Vector.

Record CPSR : Set := mkCPSR{
  IRQ_DISABLE : bool;
  FIQ_DISABLE : bool;
  USER_MODE : bool;
  FIQ_MODE : bool;
  SUPERVISOR_MODE : bool;
  UNDEF_MODE : bool
}.

Record HAL_SavedRegisters : Set := mkSR{
  r0 : nat;
  r1 : nat;
  r2 : nat;
  r3 : nat;
  r4 : nat;
  r5 : nat;
  r6 : nat;
  r7 : nat;
  r8 : nat;
  r9 : nat;
  r10 : nat;
  fp : nat;
  ip : nat;
  sp : nat;
  lr : nat;
  pc : nat;
  cpsr : CPSR;
  vector : nat;
  svc_lr : nat;
  svc_sp : nat
}.

Definition VectorTable := t nat.

Fixpoint nth n (v : VectorTable n) m :=
  match m with
    | 0 => match 


Record State : Set := mkST{
  reg : HAL_SavedRegisters;
  
}.
