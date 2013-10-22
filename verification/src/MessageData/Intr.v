Set Implicit Arguments.

Add LoadPath "../Kernel".
Require Import Bool.
Require Import EqNat.
Require Import MVB_def.
Require Import State.
Require Import Ba.

(* attach interrupts & enable these interrupts
 *)
Definition exit_thread (a : State) := a.

Definition standup_alarm (a : State) : State.
  assert (a1: State).
  destruct (get_wait_for_ba a); [exact (ba_init a true)|exact a].
  exact (set_standup_flag a1 false).
Defined.

Definition standup_thread (a : State) : State :=
  set_standup_alarm_count (set_standup_flag a true) (26 * ((get_this_addr a) + 15) -13).

Definition supervisory_interrupt_isr (a : State)(vector : nat)
           (data : nat) : cyg_uint32 * State :=
  (CYG_ISR_HANDLED, supervisory_interrupt_handle (set_md_notime a false)).

Definition supervisory_interrupt_dsr (a : State)(vector : nat)
           (count : nat)(data : nat) : State := a.

Definition timeout_interrup_isr (a : State)(vector : nat)
           (data : nat) : cyg_uint32 * State :=
  (CYG_ISR_HANDLED + CYG_ISR_CALL_DSR, a).

Definition timeout_interrup_dsr (a : State)(vector : nat)
           (count : nat)(data : nat) : State.
  destruct (get_frame_checkbit a).
  -set (a1 := set_wait_for_ba a true).
   destruct ((get_ba a1) && (negb (get_standup_flag a1)) && (negb (get_cs3 a1)));
     [exact (set_standup_flag a1 true)|exact a1].
  -destruct (get_cs3 a); [exact (ba_context_process a 0 (natToBITSET16 0) vector)|exact a].
Defined.

Definition errorfram_interrupt_isr (a : State)(vector : nat)
           (data : nat) : cyg_uint32 * State :=
  (CYG_ISR_HANDLED + CYG_ISR_CALL_DSR, a).

Definition errorfram_interrupt_dsr (a : State)(vector : nat)
           (count : nat)(data : nat) : State.
  destruct (get_frame_checkbit a); [|exact a].
  destruct (get_cs3 a); [|exact a].
  exact (set_cs3 a false).
Defined.

Definition mfprocess_handle (a : State)(vector : nat) : State.
  Admitted.

Definition mainframe_interrupt_isr (a : State)(vector : nat)
           (data : nat) : cyg_uint32 * State.
  set (a1 := set_wait_for_ba a false).
  set (a2 := set_last_mf a1 (get_current_mf a1)).
  assert (a3 : State).
  -destruct ((get_cs3 a2)
               && (negb (beq_UNSIGNED16 (get_current_mf a2)
                                        (get_ba_mf a2)
            ))); [|exact a2].
   exact (set_cs3 a2 false).
  -exact (CYG_ISR_HANDLED, (mfprocess_handle a3 vector)).
Defined.

Definition main_interrupt_dsr (a : State)(vector : nat)
           (count : nat)(data : nat) : State := a.

Definition sfprocess_handle (a : State)(vector : nat) : State.
  Admitted.

Definition slaveframe_interrupt_isr (a : State)(vector : nat)
           (data : nat) : cyg_uint32 * State.
  set (a1 := set_last_sf a (get_current_sf a)).
  exact (CYG_ISR_HANDLED, (sfprocess_handle a1 vector)).
Defined.

Definition slaveframe_interrupt_dsr (a : State)(vector : nat)
           (count : nat)(data : nat) : State := a.

Definition sync_interrupt_isr (a : State)(vector : nat)
           (data : nat) : cyg_uint32 * State.
  exact (CYG_ISR_HANDLED + CYG_ISR_CALL_DSR, a).
Defined.

Definition syncprocess_handle (a : State) : State.
  Admitted.

Definition sync_interrupt_dsr (a : State)(vector : nat)
           (count : nat)(data : nat) : State.
  exact (syncprocess_handle a).
Defined.

Definition notime_interrupt_isr (a : State)(vector : nat)
           (data : nat) : cyg_uint32 * State.
  exact (CYG_ISR_HANDLED, (set_md_notime a true)).
Defined.

Definition notime_interrupt_dsr (a : State)(vector : nat)
           (count : nat)(data : nat) : State := a.
