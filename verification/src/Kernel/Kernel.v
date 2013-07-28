Set Implicit Arguments.

Require Import Clock.
Require Import Scheduler.
Require Import ThreadTimer.

Record Kernel := mkK {
  sh : Scheduler;
  cl : ClockList;
  ttl : ThreadTimerList
}.

