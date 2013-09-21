Set Implicit Arguments.

Add LoadPath "../Kernel".

Require Import NPeano.
Require Import Array.
Import Vector.

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
Definition MVB_DEF_BASE_TYPE8 := nat.
Definition MVB_DEF_BASE_TYPE16 := nat.
Definition MVB_DEF_BASE_TYPE32 := nat.
Definition MVB_DEF_BASE_TYPE64 := nat.

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
Definition BITFIELD16 := MVB_DEF_BITFIELD16.

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

Definition DEVICES_SCAN_STRATEGY_ENUM_KNOWN := 0.
Definition DEVICES_SCAN_STRATEGY_ENUM_ALL := 1.

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
