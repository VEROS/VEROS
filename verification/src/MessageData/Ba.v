Set Implicit Arguments.

Add LoadPath "../Kernel".

Require Import NPeano.
Require Import EqNat.

(* The order of require shall not be changed *)
Require Import MVB_def.
Require Import State.

Definition MVB_SIZEOF_STRUCT_MVB_ADMINISTRATOR_KDL := 2.


Definition Inc_ba_context_devices_scan_j (a : State) : State :=
  set_ba_context_devices_scan_j a (S (get_ba_context_devices_scan_j a)).

Definition Inc_ba_context_devices_scan_i (a : State) : State :=
  set_ba_context_devices_scan_i a (S (get_ba_context_devices_scan_i a)).

Fixpoint ba_init_aux (a : State)(n : nat)(count : nat) : State.
  destruct n as [|n']; [exact a|].
  destruct (leb count (get_ba_context_devices_scan_i a)).
  -exact (set_ba_context_devices_scan_i a 0).
  -set (address := Array.nth BA_ADMIN_BAL_SIZE (get_devices_list a)
                             (BA_ADMIN_BAL_SIZE - n' - 1)).
   set (a1 := Inc_ba_context_devices_scan_i a).
   destruct (beq_nat address (get_ba_context_devices_scan_address a1)).
   +exact a1.
   +exact (ba_init_aux a1 n' count).
Defined.

(* device_list is a function to replace the stupid fucking list of shit *)
Definition ba_init (a : State)(b : bool) : State.
  set(a1 := set_cs3 a true).
  set(a2 := set_bp_number a1 0).
  (* mvb_device_status_16 not used *)
  set(a3 := set_ba_context a2 MVB_def.BA_CONTEXT_NOTRUNNING).
  set(a4 := set_ba_context_devices_scan_i a3 0).
  (* admin_obj not used *)
  set(a5 := set_devices_scan_strategy a4
            (Admin_Module.get_devices_scan_strategy (get_mvb_administrator a4))).
  destruct (get_devices_scan_strategy a5) as [|]; [|exact a5].
  set(known_offset := Admin_Module.get_known_devices_list_offset
                                  (get_mvb_administrator a5)).
  set(reserved_offset := Admin_Module.get_reserved_list_offset
                                  (get_mvb_administrator a5)).
  set(KDL_base := (if (beq_nat known_offset reserved_offset)
                   then 0
                   else (Admin_Module.get_known_devices_list
                           (get_mvb_administrator a5))
                  )
     ).
  set(count := (reserved_offset - known_offset) / 2).
  set(a6 := ba_init_aux a5 BA_ADMIN_BAL_SIZE count).
  destruct (get_ba_context_devices_scan_i a6) as [|n']; [exact a6|].
  exact (set_ba_context_devices_scan_i a6 n').
Defined.

Inductive RS_CODE_DEVICE_SCAN := RS_CODE_DEVICE_SCAN_OK | RS_CODE_DEVICE_SCAN_FIN.

Inductive RS_CODE_MASTERSHIP_TRANSFER :=
  |RS_CODE_MASTERSHIP_TRANSFER_STATES_OK
  |RS_CODE_MASTERSHIP_TRANSFER_STATES_ERROR
  |RS_CODE_MASTERSHIP_TRANSFER_KEEP
  |RS_CODE_MASTERSHIP_TRANSFER_INTERIM_TIMEOUT
  |RS_CODE_MASTERSHIP_TRANSFER_REMOTE_REJECT
  |RS_CODE_MASTERSHIP_TRANSFER_WORK.

Definition md_context_process(a : State)(vector : UNSIGNED8) : State.
  (* Due to the fact that the code called by this function is never run,
   * So, I'm going to skip this. Oh yeah, fuck youk, stupid message date.
   *)
  exact a.
Defined.

Definition build_list_of_devices_scan (a : State)(address : UNSIGNED16)
           (status : BITSET16)(flag_remove : bool) : State.
  (* TODO *)
  exact a.
Admitted.

Definition Inc_ba_context_devices_scan_address (a : State) : State :=
  set_ba_context_devices_scan_address a (S (get_ba_context_devices_scan_address a)).

Definition devices_scan(a : State)(sf_f_code : UNSIGNED8)(sf_content_16 : UNSIGNED16)
           (vector : UNSIGNED8) : RS_CODE_DEVICE_SCAN * State.
  destruct (get_device_scan_unit a) as [|]; [exact (RS_CODE_DEVICE_SCAN_FIN, a)| ].
  assert (a1 : State).
  -destruct (beq_nat vector EXTI_SUPERVISORY_INT_VECTOR) as [|];
    [exact (set_ba_context_devices_scan_j a 0)|exact a].
  -assert (a2 : State).
   +destruct (beq_nat vector EXTI_TIMEOUT_VECTOR).
    *exact (Inc_ba_context_devices_scan_j
              (build_list_of_devices_scan a1 (FRAME_ADDRESS (get_current_mf a1))
                                          (natToBITSET16 0) true)
              ).
    *destruct (beq_nat vector EXTI_SLAVE_FRAME_VECTOR).
     exact (Inc_ba_context_devices_scan_j
              (build_list_of_devices_scan a1 (FRAME_ADDRESS (get_current_mf a1))
                                          sf_content_16 true)
              ).
     exact a1.
   +destruct (leb (get_device_scan_unit a2)
                      (get_ba_context_devices_scan_j a2));
     [exact (RS_CODE_DEVICE_SCAN_FIN, a2)|].
    assert(a3 : State).
    *destruct (get_devices_scan_strategy a2).
     set(known_offset := Admin_Module.get_known_devices_list_offset
                           (get_mvb_administrator a2)).
     set(reserved_offset := Admin_Module.get_reserved_list_offset
                              (get_mvb_administrator a2)).
     set(KDL_base := (if (beq_nat known_offset reserved_offset)
                      then 0
                      else (Admin_Module.get_known_devices_list
                              (get_mvb_administrator a2))
                     )
        ).
     set(count := (reserved_offset - known_offset) / 2).

     assert(a4 : State).
     destruct (leb count (get_ba_context_devices_scan_i a2));
       [exact (set_ba_context_devices_scan_i a2 0)|exact a2].
     exact (Inc_ba_context_devices_scan_i
              (set_ba_context_devices_scan_address
                 a4 (KDL_base + (get_ba_context_devices_scan_i a4) *
                                MVB_SIZEOF_STRUCT_MVB_ADMINISTRATOR_KDL)
              )
           ).
     assert (a4 : State).
     destruct (orb (leb 4096 (get_ba_context_devices_scan_address a2))
                   (leb (get_ba_context_devices_scan_address a2) 0)); [|exact a2].
     exact (set_ba_context_devices_scan_address a2 1).
     exact (Inc_ba_context_devices_scan_address a4).
    *exact (RS_CODE_DEVICE_SCAN_OK, a3).
Defined.

Definition mastership_transfer(a : State)(sf_f_code : UNSIGNED8)(sf_content_16 : UNSIGNED16)
           (vector : UNSIGNED8) : RS_CODE_DEVICE_SCAN * State.
  Admitted.

Definition ba_context_process(a : State)(sf_f_code : UNSIGNED8)
           (sf_content_16 : UNSIGNED16)(vector : UNSIGNED8) : State.
  destruct (get_ba_context a) as [ | | | ]; [exact a| | |exact a].
  -(* BA_CONTEXT_DEVICES_SCAN *)
    set (temp := devices_scan a sf_f_code sf_content_16 vector).
    destruct (fst temp); [exact (snd temp)|].
    (* RS_CODE_DEVICE_SCAN_FIN *)
    exact (set_ba_context (snd temp) BA_CONTEXT_MESSAGE_ARBITRATION).
  -(* BA_CONTEXT_MASTERSHIP_TRANSFER *)
    exact (snd (mastership_transfer a sf_f_code sf_content_16 vector)).
Defined.

Definition supervisory_interrupt_handle (a : State) : State.
  Admitted.