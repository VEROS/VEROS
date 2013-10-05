Set Implicit Arguments.

Add LoadPath "../Kernel".

Require Import NPeano.
Require Import Array.
Import Vector.

Definition char := nat.

(********************************* MVB_def *********************************)
(* F_code mapping *)
Definition FRAME_F_CODE_0 := 0.
Definition FRAME_F_CODE_1 := 1.
Definition FRAME_F_CODE_2 := 2.
Definition FRAME_F_CODE_3 := 3.
Definition FRAME_F_CODE_4 := 4.
Definition FRAME_F_CODE_5 := 5.
Definition FRAME_F_CODE_6 := 6.
Definition FRAME_F_CODE_7 := 7.
Definition FRAME_F_CODE_8 := 8.
Definition FRAME_F_CODE_9 := 9.
Definition FRAME_F_CODE_10 := 10.
Definition FRAME_F_CODE_11 := 11.
Definition FRAME_F_CODE_12 := 12.
Definition FRAME_F_CODE_13 := 13.
Definition FRAME_F_CODE_14 := 14.
Definition FRAME_F_CODE_15 := 15.
Definition FRAME_F_CODE content := content / (2 ^ 12).
Definition FRAME_ADDRESS content :=  content mod (2 ^ 12).

(* BA states *)
Inductive BA_STATE :=
|STANDBY_MASTER : BA_STATE
|REGULAR_MASTER : BA_STATE
|FIND_NEXT : BA_STATE
|INTERIM_MASTER : BA_STATE.

(* data types *)
Definition MVB_DEF_BASE_TYPE8 := array bool 8.
Definition MVB_DEF_BASE_TYPE16 := array bool 16.
Definition MVB_DEF_BASE_TYPE32 := array bool 32.
Definition MVB_DEF_BASE_TYPE64 := array bool 64.

(* data types with less than 8-bits *)
Definition BOOLEAN1 := MVB_DEF_BASE_TYPE8.
Definition ANTIVALENT := MVB_DEF_BASE_TYPE8.
Definition BCD4 := MVB_DEF_BASE_TYPE8.
Definition ENUM4 := MVB_DEF_BASE_TYPE8.

 (* 8-bit data types *)
Definition BITSET8 := MVB_DEF_BASE_TYPE8.
Definition WORD8 := MVB_DEF_BASE_TYPE8.
Definition ENUM8 := MVB_DEF_BASE_TYPE8.
Definition UNSIGNED8 := MVB_DEF_BASE_TYPE8.
Definition INTEGER8 := MVB_DEF_BASE_TYPE8.
Definition CHARACTER8 := MVB_DEF_BASE_TYPE8.

(* 16-bit data types *)
Definition BITSET16 := MVB_DEF_BASE_TYPE16.
Definition WORD16 := MVB_DEF_BASE_TYPE16.
Definition ENUM16 := MVB_DEF_BASE_TYPE16.
Definition UNSIGNED16 := MVB_DEF_BASE_TYPE16.
Definition INTEGER16 := MVB_DEF_BASE_TYPE16.
Definition BIPOLAR2_16 := MVB_DEF_BASE_TYPE16.
Definition UNIPOLAR2_16 := MVB_DEF_BASE_TYPE16.
Definition BIPOLAR4_16 := MVB_DEF_BASE_TYPE16.

(* 32-bit data types *)
Definition REAL32 := nat. (* should be float *)
Definition BITSET32 := MVB_DEF_BASE_TYPE32.
Definition WORD32 := MVB_DEF_BASE_TYPE32.
Definition ENUM32 := MVB_DEF_BASE_TYPE32.
Definition UNSIGNED32 := MVB_DEF_BASE_TYPE32.
Definition INTEGER32 := MVB_DEF_BASE_TYPE32.

(* 64-bit data types *)
Definition BITSET64 := MVB_DEF_BASE_TYPE64.
Definition WORD64 := MVB_DEF_BASE_TYPE64.
Definition ENUM64 := MVB_DEF_BASE_TYPE64.
Definition UNSIGNED64 := MVB_DEF_BASE_TYPE64.
Definition INTEGER64 := MVB_DEF_BASE_TYPE64.

(* Structured Data Types *)
Record BITSET256 := mkBS256{
                        byte : array BITSET8 32
                        }.
Record TIMEDATA48 := mkTD{
                         seconds : UNSIGNED32;
                         ticks : UNSIGNED16
                       }.
Record STRING32 := mkS32{
                       character : array CHARACTER8 32
                     }.

Definition MVB_DEF_BITFIELD16 := UNSIGNED16.
Definition BITFIELD16 := bool. (* MVB_DEF_BITFIELD16 *)

(* Global Structures Declaration *)
Definition MAX_NUMBER_OF_BIN_ENTRIES := 64. (* 4 Entries per MVB, max 16 MVBs *)
Definition LENGTH_OF_PROJECT_STRINGS := 16. (*16 chars for Project strings*)
Definition PORTADDRESS_MASK := 4095.

(* caution: this should be 0xF000, but Coq would exit on this. So I use 0 here. *)
Definition FCODE_MASK := 0.

Definition SRC_MASK := 2048.
Definition SNK_MASK := 1024.
Definition BA_MASK := 160.
Definition LINE_MASK := 12.

(* caution : data types should not be nat. Check the C code *)
Module Header_Module.
Record Header := mkHeader {
                     checksum : nat;
                     reserved1: nat;
                     size : nat;
                     reserved2 : nat;
                     reserved3 : nat;
                     header_size : nat;
                     project_name : array nat 16;
                     project_version : array nat 16;
                     project_date : array nat 16;
                     nr_entries : nat;
                     entry_offset : array nat MAX_NUMBER_OF_BIN_ENTRIES
                   }.
End Header_Module.

Module Control_Module.
Record Mvb_Control := mkMC{
                          bus_id : nat;
                          reserved1 : nat;
                          device_address : nat;
                          reserved2 : nat;
                          t_ignore : nat;
                          reserved3 : nat;
                          code : nat
                        }.
End Control_Module.

Module Admin_Module.
Record MVB_Administrator := mkMA{
                                bus_id : nat;
                                reserved1 : nat;
                                checkword0 : nat;
                                configuration_version : nat;
                                t_reply_max : nat;
                                macro_cycles : nat;
                                event_poll_strategy : nat;
                                basic_period : nat;
                                macrocycles_per_turn : nat;
                                devices_scan_strategy : nat;
                                reserved2 : nat;
                                reserved3 : nat;
                                reserved4 : nat;
                                reserved5 : nat;
                                known_devices_list_offset : nat;
                                reserved_list_offset : nat;
                                periodic_list_offset : nat;
                                bus_administrators_list_offset : nat;
                                devices_scan_list_offset : nat;
                                end_list_offset : nat;

                                known_devices_list : nat; (* a pointer *)
                                cycle_lists_offsets : array nat 11;
                                cycle_lists_size : array nat 11;
                                split_lists_offsets : array nat 5;

                                cycle_lists : array nat 11; (* array of pointers *)

                                split_2 : array nat 4;
                                split_4 : array nat 4;
                                split_8 : array nat 16;
                                split_16 : array nat 16;
                                split_32 : array nat 64;
                                split_64 : array nat 64;
                                split_128 : array nat 256;
                                split_256 : array nat 256;
                                split_512 : array nat 1024;
                                split_1024 : array nat 1024;

                                (* three pointers folllowing *)
                                bus_administrators_list : nat;
                                device_scan_list_count0 : nat;
                                device_scan_list_count1 : nat
                              }.
End Admin_Module.

Inductive Device_scan_strategy :=
|DEVICES_SCAN_STRATEGY_ENUM_KNOWN : Device_scan_strategy
|DEVICES_SCAN_STRATEGY_ENUM_ALL : Device_scan_strategy.

(* three enums defined in hal.h *)
Inductive Frame_checkbit :=
  |MAIN_FRAME : Frame_checkbit
  |SLAVE_FRAME : Frame_checkbit.

Inductive Sync_checkbit :=
  |SYNC_STATUS : Sync_checkbit
  |SYNC_ADDRESS : Sync_checkbit.

Record Ports_Configuration := mkPC{
                                  nr_ports : nat;

                                  (* two pointers *)
                                  ports_info_0 : nat;
                                  ports_info_1 : nat
                                }.

Module Md_Module.
  Record Md_Control := mkMdC{
                         max_call_number : nat;
                         max_inst_numbery : nat;
                         default_reply_timeout : nat;
                         reserverd1 : nat;
                         my_credit : nat
                       }.
End Md_Module.

Record Function_Directory := mkFD{
                                 clear_directory : nat;
                                 nr_functions : nat;

                                 (* two pointers *)
                                 function_id : nat;
                                 station_id : nat
                               }.

Record MVB_DEVICE_STATUS := mkMDS{
                                (* common flags *)
                                ser : BITFIELD16;
                                dnr : BITFIELD16;
                                frc : BITFIELD16;
                                erd : BITFIELD16;
                                sdd : BITFIELD16;
                                ssd : BITFIELD16;
                                rld : BITFIELD16;
                                lat : BITFIELD16;

                                (* class specific *)
                                cs3 : BITFIELD16;
                                cs2 : BITFIELD16;
                                cs1 : BITFIELD16;
                                cs0 : BITFIELD16;

                                (* capability *)
                                md  : BITFIELD16;
                                gw  : BITFIELD16;
                                ba  : BITFIELD16;
                                sp  : BITFIELD16
                              }.

Definition mds_get_field mds n :=
  match n with
      |0 => mds.(ser)
      |1 => mds.(dnr)
      |2 => mds.(frc)
      |3 => mds.(erd)
      |4 => mds.(sdd)
      |5 => mds.(ssd)
      |6 => mds.(rld)
      |7 => mds.(lat)
      |8 => mds.(cs3)
      |9 => mds.(cs2)
      |10 => mds.(cs1)
      |11 => mds.(cs0)
      |12 => mds.(md)
      |13 => mds.(gw)
      |14 => mds.(ba)
      |_ => mds.(sp)
  end.

Definition mds_set_field mds n v :=
  match mds with
      |mkMDS v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =>
       match n with
         |0 => mkMDS v v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
         |1 => mkMDS v0 v v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
         |2 => mkMDS v0 v1 v v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
         |3 => mkMDS v0 v1 v2 v v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
         |4 => mkMDS v0 v1 v2 v3 v v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
         |5 => mkMDS v0 v1 v2 v3 v4 v v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
         |6 => mkMDS v0 v1 v2 v3 v4 v5 v v7 v8 v9 v10 v11 v12 v13 v14 v15
         |7 => mkMDS v0 v1 v2 v3 v4 v5 v6 v v8 v9 v10 v11 v12 v13 v14 v15
         |8 => mkMDS v0 v1 v2 v3 v4 v5 v6 v7 v v9 v10 v11 v12 v13 v14 v15
         |9 => mkMDS v0 v1 v2 v3 v4 v5 v6 v7 v8 v v10 v11 v12 v13 v14 v15
         |10 => mkMDS v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v v11 v12 v13 v14 v15
         |11 => mkMDS v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v v12 v13 v14 v15
         |12 => mkMDS v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v v13 v14 v15
         |13 => mkMDS v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v v14 v15
         |14 => mkMDS v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v v15
         |_  => mkMDS v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v
       end
  end.

(* --------------------------------------------------------------------------
 *  Bit Constants : SV_MVB_DEVICE_STATUS_BIT_xxx
 *
 *  Purpose       : MVB device status.
 * --------------------------------------------------------------------------
 *)
(* capabilities *)
Definition MVB_DEVICE_STATUS_BIT_SP := 32768. (* special device (class1=0)   *)
Definition MVB_DEVICE_STATUS_BIT_BA := 16384. (* bus administrator           *)
Definition MVB_DEVICE_STATUS_BIT_GW := 8192. (* gateway                     *)
Definition MVB_DEVICE_STATUS_BIT_MD := 4096. (* message data                *)

(* class specific (general) *)
Definition MVB_DEVICE_STATUS_BIT_CS0 := 2048. (* first  bit ...  ...of       *)
Definition MVB_DEVICE_STATUS_BIT_CS1 := 1024. (* second bit ...    class     *)
Definition MVB_DEVICE_STATUS_BIT_CS2 := 512. (* third  bit ...   specific   *)
Definition MVB_DEVICE_STATUS_BIT_CS3 := 256. (* fourth bit ...    field     *)

(* class specific (bus administrator) *)

Definition MVB_DEVICE_STATUS_BIT_AX1 := 2048.
(* second last significant bit *)
(* of the actualisation key *)
(* of the periodic list *)

Definition MVB_DEVICE_STATUS_BIT_AX0 := 1024.
(* least significant bit of    *)
(*  the actualisation key of   *)
(*  the periodic list          *)

Definition MVB_DEVICE_STATUS_BIT_ACT := 512.
(* device is actualised and in *)
(*  condition of becoming      *)
(* master                      *)

Definition MVB_DEVICE_STATUS_BIT_MAS := 256.
(* device is the current       *)
(*  master                     *)


(* class specific (gateway without bus administrator capability) *)
Definition MVB_DEVICE_STATUS_BIT_STD := 2048. (* static disturbance          *)
Definition MVB_DEVICE_STATUS_BIT_DYD := 0. (* dynamic disturbance         *)

(* common flags *)
Definition MVB_DEVICE_STATUS_BIT_LAT := 128. (* line A trusted              *)
Definition MVB_DEVICE_STATUS_BIT_RLD := 64. (* redundant line disturbed    *)
Definition MVB_DEVICE_STATUS_BIT_SSD := 32. (* some system disturbance     *)
Definition MVB_DEVICE_STATUS_BIT_SDD := 16. (* some device disturbance     *)
Definition MVB_DEVICE_STATUS_BIT_ERD := 8. (* extended reply delay        *)
Definition MVB_DEVICE_STATUS_BIT_FRC := 4. (* forced device               *)
Definition MVB_DEVICE_STATUS_BIT_DNR := 2. (* device not ready            *)
Definition MVB_DEVICE_STATUS_BIT_SER := 1. (* system reserved             *)

Require Thread.
Require Alarm.

Definition cyg_uint32 := nat.
Definition SA_STACK_SIZE := 256.
Definition cyg_thread := Thread.Thread.
Definition cyg_handle_t := nat. (* should be pointers, actually *)

Definition MVB_ADMINISTRATOR := Admin_Module.MVB_Administrator.
Definition cyg_uint16 := MVB_ADMINISTRATOR. (* They are the same, for there is only 16 bits. *)
Definition cyg_alarm := Alarm.Alarm.
Definition cyg_tick_count_t := nat.

(********************************** Message_data *******************************)

Record MD_ABILITY_NODE := mkMAN{
                              pre_high : UNSIGNED8; (* init as 4 *)
                              next_high : UNSIGNED8; (* init as 4*)
                              pre_low : UNSIGNED8; (* init as 8 *)
                              next_low : UNSIGNED8 (* init as 8 *)
                            }.

Record Message_data := mkMD{
                           (* this_addr : UNSIGNED16; defined in init *)
                           (* mvb_device_status : MVB_DEVICE_STATUS; defined in init *)
                           (* current_mf : UNSIGNED16; defined in intr *)
                           (* current_sf : UNSIGNED16; defined in intr *)
                           (* ba_mf : UNSIGNED16; defined in ba*)
                           current_index : nat (* init as 0 *)
                         }.

(* MD_ABILITY_NODE, md_ability_array, get & set macros are defined in
 * Message_data.h, but never referenced anywhere other than in ba.c.
 *)

(* md_ability_count,is defined in Message_data.h, but never referenced
 * anywhere other than in ba.c.
 *)

(********************************** ba *************************************)

Inductive Ba_context :=
|BA_CONTEXT_NOTRUNNING : Ba_context
|BA_CONTEXT_DEVICES_SCAN : Ba_context
|BA_CONTEXT_MASTERSHIP_TRANSFER : Ba_context
|BA_CONTEXT_MESSAGE_ARBITRATION : Ba_context.

Definition BA_ADMIN_BAL_SIZE := 64 + 1.

Record Ba := mkBa{
                 bp_number : nat; (* init as 0 *)
                 ba_context : Ba_context; (* should be UNSIGNED8 *)
                 ba_mf : UNSIGNED16;
                 device_scan_unit : UNSIGNED8;

                 ba_context_devices_scan_i : UNSIGNED8;
                 ba_context_devices_scan_j : UNSIGNED8;
                 ba_context_devices_scan_address : UNSIGNED16;
                 ba_context_mastership_transfer_address : UNSIGNED16;
                 ba_context_mastership_transfer_act : UNSIGNED8;

                 (* should be a pointer of MVB_ADMINISTRATOR *)
                 admin_obj : nat;

                 (* should be ENUM16 *)
                 devices_scan_strategy : Device_scan_strategy;
                 devices_list : array cyg_uint16 BA_ADMIN_BAL_SIZE;

                 (* should be cyg_uint16[BA_ADMIN_BAL_SIZE] *)
                 devices_list_timeout_count : array nat BA_ADMIN_BAL_SIZE;

                 md_ability_array : array MD_ABILITY_NODE 4096;

                 md_ability_count : nat (* should be UNSIGNED8 *)

                 (* this_addr : UNSIGNED8;
                  * it is defined in intr.c, thought it is referenced in many other
                  * files
                  *)

                 (* mvb_administrator : MVB_ADMINISTRATOR; defined in init *)

                 (* mvb_device_status : MVB_DEVICE_STATUS; defined in init *)

                 (* mvb_device_status_16 : cyg_uint16; defined in init *)

                 (* current_mf : UNSIGNED16 *)
               }.

(******************************** Intr *************************************)

Record Intr := mkIntr{
                 wait_for_ba : bool;
                 frame_checkbit : Frame_checkbit;
                 sync_checkbit : Sync_checkbit;
                 sync_interrupt_flag : bool;

                 current_mf : UNSIGNED16;
                 last_mf : UNSIGNED16;
                 current_sf : UNSIGNED16;
                 last_sf : UNSIGNED16;

                 standup_stack : array char SA_STACK_SIZE;

                 standup_thread_data : cyg_thread;
                 standup_thread_handle : cyg_handle_t;
                 standup_flag := nat; (* 0 for initialization *)

                 (* this_akey : UNSIGNED16; defined in init *)
                 (* this_addr : UNSIGNED16; defined in init *)

                 (* mvb_administrator : MVB_ADMINISTRATOR; defined in init *)
                 (* mvb_device_status : MVB_DEVICE_STATUS; defined in init *)

                 (* mvb_device_status_16 : cyg_uint16; defined in init *)
                 (* ba_mf : UNSIGNED16; defined in ba *)

                 standup_counter_handle : cyg_handle_t;
                 standup_alarm_count : cyg_tick_count_t;

                 standup_alarm_object : cyg_alarm;

                 standup_alarm_handle : cyg_handle_t;
                 md_notime : bool
               }.

(***************************** Init ****************************)

Record Init := mkInit{
                   header : Header_Module.Header;
                   mvb_control : Control_Module.Mvb_Control;
                   mvb_administrator : Admin_Module.MVB_Administrator;
                   ports_Configuration : Ports_Configuration;
                   md_control : Md_Module.Md_Control;
                   function_directory : Function_Directory;
                   mvb_device_status : MVB_DEVICE_STATUS;
                   mvb_device_status_16 : cyg_uint16;
                   MVB_CONTROL_FLAG : bool; (* should be unsigned short *)
                   MVB_ADMINISTRATOR_FLAG : bool; (* should be unsigned short *)
                   PORTS_CONFIGURATION_FLAG : bool; (* should be unsigned short *)
                   MD_CONTROL_FLAG : bool; (* should be unsigned short *)
                   FUNCTION_DIRECTORY_FLAG : bool; (* should be unsigned short *)
                   this_akey : nat; (* should be unsigned short *)
                   this_addr : nat
                 }.

Definition init_set_mvb_device_status i m :=
  match i with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
             => mkInit a0 a1 a2 a3 a4 a5 m a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition init_set_mvb_device_status_16 i m :=
  match i with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
             => mkInit a0 a1 a2 a3 a4 a5 a6 m a8 a9 a10 a11 a12 a13 a14
  end.

(******************************* Main ********************************)

Definition STACK_SIZE := 256.
Record Main := mkMain{
                   exti_stack : array nat STACK_SIZE; (* should be char[] *)
                   start_stack : array nat STACK_SIZE; (* should be char[] *)
                   start_thread_data : cyg_thread;
                   exti_thread_data : cyg_thread;
                   start_thread_handle : cyg_handle_t;
                   exti_thread_handle : cyg_handle_t;
                   led_stack : array nat STACK_SIZE; (* should be char[] *)
                   led_thread_data : cyg_thread;
                   led_thread_handle : cyg_handle_t
                   (* mvb_device_status : MVB_DEVICE_STATUS defined in init *)
                 }.

Record State := mkState{
                    message_data : Message_data;
                    ba_state : Ba;
                    intr : Intr;
                    init : Init;
                    main : Main
                  }.

Definition set_message s m :=
  mkState m s.(ba_state) s.(intr) s.(init) s.(main).

Definition set_ba s b :=
  mkState s.(message_data) b s.(intr) s.(init) s.(main).

Definition set_intr s i :=
  mkState s.(message_data) s.(ba_state) i s.(init) s.(main).

Definition set_init s i :=
  mkState s.(message_data) s.(ba_state) s.(intr) i s.(main).

Definition set_main s m :=
  mkState s.(message_data) s.(ba_state) s.(intr) s.(init) m.

Definition get_frame_checkbit s := s.(intr).(frame_checkbit).

Definition get_mvb_device_status s := s.(init).(mvb_device_status).

Definition set_mvb_device_status s m :=
  set_init s (init_set_mvb_device_status s.(init) m).

Definition set_mvb_device_status_16 s m :=
  set_init s (init_set_mvb_device_status_16 s.(init) m).