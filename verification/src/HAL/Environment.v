(**
This file defines CPU and states for VEROS
Author: Shengpeng Liu 
Date: May 24, 2013
*)

Require Import Bool.
Require Import EqNat.

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

  Definition get_core_register cr n :=
    match n with
      |0 => cr.(r0)
      |1 => cr.(r1)
      |2 => cr.(r2)
      |3 => cr.(r3)
      |4 => cr.(r4)
      |5 => cr.(r5)
      |6 => cr.(r6)
      |7 => cr.(r7)
      |8 => cr.(r8)
      |9 => cr.(r9)
      |10 => cr.(r10)
      |11 => cr.(r11)
      |12 => cr.(r12)
      |13 => cr.(r13)
      |14 => cr.(r14)
      |_ => cr.(r15)               
    end.

  Definition set_core_register cr n v :=
    match cr with mkCR s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 =>
                    match n with
                      |0 => mkCR v s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
                      |1 => mkCR s0 v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
                      |2 => mkCR s0 s1 v s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
                      |3 => mkCR s0 s1 s2 v s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
                      |4 => mkCR s0 s1 s2 s3 v s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
                      |5 => mkCR s0 s1 s2 s3 s4 v s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
                      |6 => mkCR s0 s1 s2 s3 s4 s5 v s7 s8 s9 s10 s11 s12 s13 s14 s15
                      |7 => mkCR s0 s1 s2 s3 s4 s5 s6 v s8 s9 s10 s11 s12 s13 s14 s15
                      |8 => mkCR s0 s1 s2 s3 s4 s5 s6 s7 v s9 s10 s11 s12 s13 s14 s15
                      |9 => mkCR s0 s1 s2 s3 s4 s5 s6 s7 s8 v s10 s11 s12 s13 s14 s15
                      |10 => mkCR s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 v s11 s12 s13 s14 s15
                      |11 => mkCR s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 v s12 s13 s14 s15
                      |12 => mkCR s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v s13 s14 s15
                      |13 => mkCR s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 v s14 s15
                      |14 => mkCR s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 v s15
                      |_  => mkCR s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 v
                    end
    end.

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

  Definition get_core hs n := get_core_register hs.(core) n.

  Definition set_core hs n v := 
    mkSR (set_core_register hs.(core) n v) hs.(psr) hs.(vector) hs.(basepri) hs.(xlr).
  
  Definition get_psr hs := hs.(psr).

  Definition set_psr hs npsr :=
    mkSR hs.(core) npsr hs.(vector) hs.(basepri) hs.(xlr).

  Definition get_vector hs := hs.(vector).

  Definition set_vector hs vec :=
    mkSR hs.(core) hs.(psr) vec hs.(basepri) hs.(xlr).

  Definition get_basepri hs := hs.(basepri).

  Definition set_basepri hs n := 
    mkSR hs.(core) hs.(psr) hs.(vector) n hs.(xlr).

  Definition get_xlr hs := hs.(xlr).

  Definition set_xlr hs n :=
    mkSR hs.(core) hs.(psr) hs.(vector) hs.(basepri) n.
  
End CPU.
