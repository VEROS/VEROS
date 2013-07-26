Set Implicit Arguments.

Require Import Clock.
Require Import Scheduler.

Record Kernel := mkK {
  sh : Scheduler;
  cl : ClockList
}.


