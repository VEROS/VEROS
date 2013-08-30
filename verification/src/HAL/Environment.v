(**
This file defines CPU and states for VEROS
Author: Shengpeng Liu 
Date: May 24, 2013
*)

Require Import Bool.
Require Import EqNat.
Require Import Constants.

Section CPU.

  Record CoreRegister := mkCR {
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
    r11 : nat;
    r12 : nat;
    r13 : nat; (*sp*)
    r14 : nat; (*lr*)
    r15 : nat (*pc*)
  }.  

  Record APSR : Type := mkAPSR {
    N : bool; (*Negative*)
    Z : bool; (*Zero*)
    C : bool; (*Carry*)
    V : bool; (*Overflow*)
    Q : bool  (*Sticky Saturation*)
  }.

  Record EPSR : Type := mkEPSR {
    TCI_IT : bool; (*related to conditional branching*)
    T : bool       (*Thumb*)
  }.
  
  Record PSR : Type := mkpsr {
    apsr : APSR;
    isr : nat; (*isr number, 0-255, occupying 9 bits*)
    epsr : EPSR
  }.
  
  Record HAL_SavedRegisters : Type := mkSR {
    core : CoreRegister;
    psr : PSR;
    vector : nat;
    basepri : nat;
    xlr : nat
  }.

  Definition get_pc (r : HAL_SavedRegisters) : nat :=
    r.(core).(r15).
  
End CPU.

(*Assumed Defintiions*)
Variable Thread : Type.
Variable VSR : Type.
Variable ISR : Type.
Variable Data : Type.
Variable Object : Type.

Variable hal_vsr_table : nat -> VSR.

Record HardState : Type := mkHST {
  regs : HAL_SavedRegisters;
  TList : nat -> Thread;
  hal_isr_handlers : nat -> ISR;
  hal_isr_Data : nat -> Data;
  hal_isr_Object : nat -> Object;

  contextPtr : nat -> HAL_SavedRegisters
}.

Definition CYGARC_HAL_GET_PC_REG (s: HardState) : nat :=
  get_pc (regs s).

Definition HAL_THREAD_LOAD_CONTEXT (tspptr : nat)(s : HardState) : HardState :=
  match s with
  mkHST _ l h d o c => (mkHST (c tspptr) l h d o c)
  end.

Definition update_contexPtr (fspptr: nat)(r : HAL_SavedRegisters)(c : nat -> HAL_SavedRegisters) 
: nat -> HAL_SavedRegisters :=
  fun(n : nat) => if (beq_nat n fspptr) then r else c n. 

Definition HAL_THREAD_SWITCH_CONTEXT (fspptr : nat)(tspptr : nat)(s: HardState) : HardState :=
  match s with
  mkHST r l h d o c => (mkHST (c tspptr) l h d o (update_contexPtr fspptr r c))
  end.

(*Not clear about the behavior yet, neet to check*)
Variable HAL_THREAD_INIT_CONTEXT : nat -> nat -> nat-> nat -> HAL_SavedRegisters.