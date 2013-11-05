Set Implicit Arguments.

Add LoadPath "../Kernel".

Require Import NPeano.
Require Import Array.
Import Vector.

Definition char := nat.

(********************************* MVB_def *********************************)
(* F_code mapping *)
Inductive FRAME_F_CODE_CONST :=
  |FRAME_F_CODE_0 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_1 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_2 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_3 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_4 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_5 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_6 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_7 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_8 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_9 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_10 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_11 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_12 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_13 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_14 : FRAME_F_CODE_CONST
  |FRAME_F_CODE_15 : FRAME_F_CODE_CONST.

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
Definition UNSIGNED8 := nat.
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

Definition get_byte a := a.(byte).

Definition set_byte a v :=
  match a with
      mkBS256 a0
      => mkBS256 v
  end.

Record TIMEDATA48 := mkTD{
                         seconds : UNSIGNED32;
                         ticks : UNSIGNED16
                       }.

Definition get_seconds a := a.(seconds).

Definition set_seconds a v :=
  match a with
      mkTD a0 a1
      => mkTD v a1
  end.

Definition get_ticks a := a.(ticks).

Definition set_ticks a v :=
  match a with
      mkTD a0 a1
      => mkTD a0 v
  end.

Record STRING32 := mkS32{
                       character : array CHARACTER8 32
                     }.

Definition get_character a := a.(character).

Definition set_character a v :=
  match a with
      mkS32 a0
      => mkS32 v
  end.

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
  Record Header := mkHeader{
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

  Definition get_checksum a := a.(checksum).

  Definition set_checksum a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    end.

  Definition get_reserved1 a := a.(reserved1).

  Definition set_reserved1 a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader a0 v a2 a3 a4 a5 a6 a7 a8 a9 a10
    end.

  Definition get_size a := a.(size).

  Definition set_size a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader a0 a1 v a3 a4 a5 a6 a7 a8 a9 a10
    end.

  Definition get_reserved2 a := a.(reserved2).

  Definition set_reserved2 a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader a0 a1 a2 v a4 a5 a6 a7 a8 a9 a10
    end.

  Definition get_reserved3 a := a.(reserved3).

  Definition set_reserved3 a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader a0 a1 a2 a3 v a5 a6 a7 a8 a9 a10
    end.

  Definition get_header_size a := a.(header_size).

  Definition set_header_size a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader a0 a1 a2 a3 a4 v a6 a7 a8 a9 a10
    end.

  Definition get_project_name a := a.(project_name).

  Definition set_project_name a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader a0 a1 a2 a3 a4 a5 v a7 a8 a9 a10
    end.

  Definition get_project_version a := a.(project_version).

  Definition set_project_version a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader a0 a1 a2 a3 a4 a5 a6 v a8 a9 a10
    end.

  Definition get_project_date a := a.(project_date).

  Definition set_project_date a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader a0 a1 a2 a3 a4 a5 a6 a7 v a9 a10
    end.

  Definition get_nr_entries a := a.(nr_entries).

  Definition set_nr_entries a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 v a10
    end.

  Definition get_entry_offset a := a.(entry_offset).

  Definition set_entry_offset a v :=
    match a with
        mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        => mkHeader a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v
    end.

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

  Definition get_bus_id a := a.(bus_id).

  Definition set_bus_id a v :=
    match a with
        mkMC a0 a1 a2 a3 a4 a5 a6
        => mkMC v a1 a2 a3 a4 a5 a6
    end.

  Definition get_reserved1 a := a.(reserved1).

  Definition set_reserved1 a v :=
    match a with
        mkMC a0 a1 a2 a3 a4 a5 a6
        => mkMC a0 v a2 a3 a4 a5 a6
    end.

  Definition get_device_address a := a.(device_address).

  Definition set_device_address a v :=
    match a with
        mkMC a0 a1 a2 a3 a4 a5 a6
        => mkMC a0 a1 v a3 a4 a5 a6
    end.

  Definition get_reserved2 a := a.(reserved2).

  Definition set_reserved2 a v :=
    match a with
        mkMC a0 a1 a2 a3 a4 a5 a6
        => mkMC a0 a1 a2 v a4 a5 a6
    end.

  Definition get_t_ignore a := a.(t_ignore).

  Definition set_t_ignore a v :=
    match a with
        mkMC a0 a1 a2 a3 a4 a5 a6
        => mkMC a0 a1 a2 a3 v a5 a6
    end.

  Definition get_reserved3 a := a.(reserved3).

  Definition set_reserved3 a v :=
    match a with
        mkMC a0 a1 a2 a3 a4 a5 a6
        => mkMC a0 a1 a2 a3 a4 v a6
    end.

  Definition get_code a := a.(code).

  Definition set_code a v :=
    match a with
        mkMC a0 a1 a2 a3 a4 a5 a6
        => mkMC a0 a1 a2 a3 a4 a5 v
    end.

End Control_Module.

Inductive Device_scan_strategy :=
|DEVICES_SCAN_STRATEGY_ENUM_KNOWN : Device_scan_strategy
|DEVICES_SCAN_STRATEGY_ENUM_ALL : Device_scan_strategy.

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
                                  devices_scan_strategy : Device_scan_strategy;
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
                                  known_devices_list : nat; (* should be a pointer *)
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

  Definition get_bus_id a := a.(bus_id).

  Definition set_bus_id a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_reserved1 a := a.(reserved1).

  Definition set_reserved1 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 v a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_checkword0 a := a.(checkword0).

  Definition set_checkword0 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 v a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_configuration_version a := a.(configuration_version).

  Definition set_configuration_version a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 v a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_t_reply_max a := a.(t_reply_max).

  Definition set_t_reply_max a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 v a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_macro_cycles a := a.(macro_cycles).

  Definition set_macro_cycles a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 v a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_event_poll_strategy a := a.(event_poll_strategy).

  Definition set_event_poll_strategy a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 v a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_basic_period a := a.(basic_period).

  Definition set_basic_period a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 v a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_macrocycles_per_turn a := a.(macrocycles_per_turn).

  Definition set_macrocycles_per_turn a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 v a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_devices_scan_strategy a := a.(devices_scan_strategy).

  Definition set_devices_scan_strategy a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 v a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_reserved2 a := a.(reserved2).

  Definition set_reserved2 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_reserved3 a := a.(reserved3).

  Definition set_reserved3 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 v a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_reserved4 a := a.(reserved4).

  Definition set_reserved4 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 v a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_reserved5 a := a.(reserved5).

  Definition set_reserved5 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 v a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_known_devices_list_offset a := a.(known_devices_list_offset).

  Definition set_known_devices_list_offset a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 v a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_reserved_list_offset a := a.(reserved_list_offset).

  Definition set_reserved_list_offset a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 v a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_periodic_list_offset a := a.(periodic_list_offset).

  Definition set_periodic_list_offset a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_bus_administrators_list_offset a := a.(bus_administrators_list_offset).

  Definition set_bus_administrators_list_offset a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 v a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_devices_scan_list_offset a := a.(devices_scan_list_offset).

  Definition set_devices_scan_list_offset a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 v a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_end_list_offset a := a.(end_list_offset).

  Definition set_end_list_offset a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 v a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_known_devices_list a := a.(known_devices_list).

  Definition set_known_devices_list a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 v a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_cycle_lists_offsets a := a.(cycle_lists_offsets).

  Definition set_cycle_lists_offsets a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 v a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_cycle_lists_size a := a.(cycle_lists_size).

  Definition set_cycle_lists_size a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 v a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_split_lists_offsets a := a.(split_lists_offsets).

  Definition set_split_lists_offsets a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 v a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_cycle_lists a := a.(cycle_lists).

  Definition set_cycle_lists a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 v a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_split_2 a := a.(split_2).

  Definition set_split_2 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 v a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_split_4 a := a.(split_4).

  Definition set_split_4 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 v a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_split_8 a := a.(split_8).

  Definition set_split_8 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 v a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_split_16 a := a.(split_16).

  Definition set_split_16 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 v a29 a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_split_32 a := a.(split_32).

  Definition set_split_32 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 v a30 a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_split_64 a := a.(split_64).

  Definition set_split_64 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 v a31 a32 a33 a34 a35 a36 a37
    end.

  Definition get_split_128 a := a.(split_128).

  Definition set_split_128 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 v a32 a33 a34 a35 a36 a37
    end.

  Definition get_split_256 a := a.(split_256).

  Definition set_split_256 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 v a33 a34 a35 a36 a37
    end.

  Definition get_split_512 a := a.(split_512).

  Definition set_split_512 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 v a34 a35 a36 a37
    end.

  Definition get_split_1024 a := a.(split_1024).

  Definition set_split_1024 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 v a35 a36 a37
    end.

  Definition get_bus_administrators_list a := a.(bus_administrators_list).

  Definition set_bus_administrators_list a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 v a36 a37
    end.

  Definition get_device_scan_list_count0 a := a.(device_scan_list_count0).

  Definition set_device_scan_list_count0 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 v a37
    end.

  Definition get_device_scan_list_count1 a := a.(device_scan_list_count1).

  Definition set_device_scan_list_count1 a v :=
    match a with
        mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37
        => mkMA a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 v
    end.

End Admin_Module.

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

Definition get_nr_ports a := a.(nr_ports).

Definition set_nr_ports a v :=
  match a with
      mkPC a0 a1 a2
      => mkPC v a1 a2
  end.

Definition get_ports_info_0 a := a.(ports_info_0).

Definition set_ports_info_0 a v :=
  match a with
      mkPC a0 a1 a2
      => mkPC a0 v a2
  end.

Definition get_ports_info_1 a := a.(ports_info_1).

Definition set_ports_info_1 a v :=
  match a with
      mkPC a0 a1 a2
      => mkPC a0 a1 v
  end.

Module Md_Module.
  Record Md_Control := mkMdC{
                           max_call_number : nat;
                           max_inst_numbery : nat;
                           default_reply_timeout : nat;
                           reserverd1 : nat;
                           my_credit : nat
                         }.
  Definition get_max_call_number a := a.(max_call_number).

  Definition set_max_call_number a v :=
    match a with
        mkMdC a0 a1 a2 a3 a4
        => mkMdC v a1 a2 a3 a4
    end.

  Definition get_max_inst_numbery a := a.(max_inst_numbery).

  Definition set_max_inst_numbery a v :=
    match a with
        mkMdC a0 a1 a2 a3 a4
        => mkMdC a0 v a2 a3 a4
    end.

  Definition get_default_reply_timeout a := a.(default_reply_timeout).

  Definition set_default_reply_timeout a v :=
    match a with
        mkMdC a0 a1 a2 a3 a4
        => mkMdC a0 a1 v a3 a4
    end.

  Definition get_reserverd1 a := a.(reserverd1).

  Definition set_reserverd1 a v :=
    match a with
        mkMdC a0 a1 a2 a3 a4
        => mkMdC a0 a1 a2 v a4
    end.

  Definition get_my_credit a := a.(my_credit).

  Definition set_my_credit a v :=
    match a with
        mkMdC a0 a1 a2 a3 a4
        => mkMdC a0 a1 a2 a3 v
    end.

End Md_Module.

Record Function_Directory := mkFD{
                                 clear_directory : nat;
                                 nr_functions : nat;

                                 (* two pointers *)
                                 function_id : nat;
                                 station_id : nat
                               }.

Definition get_clear_directory a := a.(clear_directory).

Definition set_clear_directory a v :=
  match a with
      mkFD a0 a1 a2 a3
      => mkFD v a1 a2 a3
  end.

Definition get_nr_functions a := a.(nr_functions).

Definition set_nr_functions a v :=
  match a with
      mkFD a0 a1 a2 a3
      => mkFD a0 v a2 a3
  end.

Definition get_function_id a := a.(function_id).

Definition set_function_id a v :=
  match a with
      mkFD a0 a1 a2 a3
      => mkFD a0 a1 v a3
  end.

Definition get_station_id a := a.(station_id).

Definition set_station_id a v :=
  match a with
      mkFD a0 a1 a2 a3
      => mkFD a0 a1 a2 v
  end.

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

Definition get_ser a := a.(ser).

Definition set_ser a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  end.

Definition get_dnr a := a.(dnr).

Definition set_dnr a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 v a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  end.

Definition get_frc a := a.(frc).

Definition set_frc a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 v a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  end.

Definition get_erd a := a.(erd).

Definition set_erd a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 v a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  end.

Definition get_sdd a := a.(sdd).

Definition set_sdd a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 v a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  end.

Definition get_ssd a := a.(ssd).

Definition set_ssd a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 v a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  end.

Definition get_rld a := a.(rld).

Definition set_rld a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 a5 v a7 a8 a9 a10 a11 a12 a13 a14 a15
  end.

Definition get_lat a := a.(lat).

Definition set_lat a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 a5 a6 v a8 a9 a10 a11 a12 a13 a14 a15
  end.

Definition get_cs3 a := a.(cs3).

Definition set_cs3 a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 a5 a6 a7 v a9 a10 a11 a12 a13 a14 a15
  end.

Definition get_cs2 a := a.(cs2).

Definition set_cs2 a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 v a10 a11 a12 a13 a14 a15
  end.

Definition get_cs1 a := a.(cs1).

Definition set_cs1 a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v a11 a12 a13 a14 a15
  end.

Definition get_cs0 a := a.(cs0).

Definition set_cs0 a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 v a12 a13 a14 a15
  end.

Definition get_md a := a.(md).

Definition set_md a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 v a13 a14 a15
  end.

Definition get_gw a := a.(gw).

Definition set_gw a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 v a14 a15
  end.

Definition get_ba a := a.(ba).

Definition set_ba a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 v a15
  end.

Definition get_sp a := a.(sp).

Definition set_sp a v :=
  match a with
      mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      => mkMDS a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 v
  end.

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
Definition cyg_uint16 := nat. (* They are the same, for there is only 16 bits. *)
Definition cyg_alarm := Alarm.Alarm.
Definition cyg_tick_count_t := nat.

(********************************** Message_data *******************************)

Record MD_ABILITY_NODE := mkMAN{
                              pre_high : UNSIGNED8; (* init as 4 *)
                              next_high : UNSIGNED8; (* init as 4*)
                              pre_low : UNSIGNED8; (* init as 8 *)
                              next_low : UNSIGNED8 (* init as 8 *)
                            }.

Definition get_pre_high a := a.(pre_high).

Definition set_pre_high a v :=
  match a with
      mkMAN a0 a1 a2 a3
      => mkMAN v a1 a2 a3
  end.

Definition get_next_high a := a.(next_high).

Definition set_next_high a v :=
  match a with
      mkMAN a0 a1 a2 a3
      => mkMAN a0 v a2 a3
  end.

Definition get_pre_low a := a.(pre_low).

Definition set_pre_low a v :=
  match a with
      mkMAN a0 a1 a2 a3
      => mkMAN a0 a1 v a3
  end.

Definition get_next_low a := a.(next_low).

Definition set_next_low a v :=
  match a with
      mkMAN a0 a1 a2 a3
      => mkMAN a0 a1 a2 v
  end.

Record Message_data := mkMD{
                           (* this_addr : UNSIGNED16; defined in init *)
                           (* mvb_device_status : MVB_DEVICE_STATUS; defined in init *)
                           (* current_mf : UNSIGNED16; defined in intr *)
                           (* current_sf : UNSIGNED16; defined in intr *)
                           (* ba_mf : UNSIGNED16; defined in ba*)
                           current_index : nat (* init as 0 *)
                         }.

Definition get_current_index a := a.(current_index).

Definition set_current_index a v :=
  match a with
      mkMD a0
      => mkMD v
  end.

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

Inductive Master_transfer :=
  |BA_CONTEXT_MASTERSHIP_TRANSFER_NULL : Master_transfer
  |BA_CONTEXT_MASTERSHIP_TRANSFER_DEVICE_STATUS : Master_transfer
  |BA_CONTEXT_MASTERSHIP_TRANSFER_OFFER_MASTERSHIP : Master_transfer.

Record Ba := mkBa{
                 bp_number : nat; (* init as 0 *)
                 ba_context : Ba_context; (* should be UNSIGNED8 *)
                 ba_mf : UNSIGNED16;
                 device_scan_unit : UNSIGNED8;

                 ba_context_devices_scan_i : UNSIGNED8;
                 ba_context_devices_scan_j : UNSIGNED8;
                 ba_context_devices_scan_address : nat;
                 ba_context_mastership_transfer_address : nat;
                 ba_context_mastership_transfer_act : Master_transfer;

                 (* should be a pointer of MVB_ADMINISTRATOR
                  * No use really. Ignore it.
                  *)
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

Definition get_bp_number a := a.(bp_number).

Definition set_bp_number a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_ba_context a := a.(ba_context).

Definition set_ba_context a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 v a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_ba_mf a := a.(ba_mf).

Definition set_ba_mf a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 v a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_device_scan_unit a := a.(device_scan_unit).

Definition set_device_scan_unit a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 v a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_ba_context_devices_scan_i a := a.(ba_context_devices_scan_i).

Definition set_ba_context_devices_scan_i a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 v a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_ba_context_devices_scan_j a := a.(ba_context_devices_scan_j).

Definition set_ba_context_devices_scan_j a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 a4 v a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_ba_context_devices_scan_address a := a.(ba_context_devices_scan_address).

Definition set_ba_context_devices_scan_address a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 a4 a5 v a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_ba_context_mastership_transfer_address a := a.(ba_context_mastership_transfer_address).

Definition set_ba_context_mastership_transfer_address a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 a4 a5 a6 v a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_ba_context_mastership_transfer_act a := a.(ba_context_mastership_transfer_act).

Definition set_ba_context_mastership_transfer_act a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 a4 a5 a6 a7 v a9 a10 a11 a12 a13 a14
  end.

Definition get_admin_obj a := a.(admin_obj).

Definition set_admin_obj a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 v a10 a11 a12 a13 a14
  end.

Definition get_devices_scan_strategy a := a.(devices_scan_strategy).

Definition set_devices_scan_strategy a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v a11 a12 a13 a14
  end.

Definition get_devices_list a := a.(devices_list).

Definition set_devices_list a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 v a12 a13 a14
  end.

Definition get_devices_list_timeout_count a := a.(devices_list_timeout_count).

Definition set_devices_list_timeout_count a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 v a13 a14
  end.

Definition get_md_ability_array a := a.(md_ability_array).

Definition set_md_ability_array a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 v a14
  end.

Definition get_md_ability_count a := a.(md_ability_count).

Definition set_md_ability_count a v :=
  match a with
      mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkBa a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 v
  end.

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
                   standup_flag : bool; (* 0 for initialization *)

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

Definition get_wait_for_ba a := a.(wait_for_ba).

Definition set_wait_for_ba a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  end.

Definition get_frame_checkbit a := a.(frame_checkbit).

Definition set_frame_checkbit a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 v a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  end.

Definition get_sync_checkbit a := a.(sync_checkbit).

Definition set_sync_checkbit a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 v a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  end.

Definition get_sync_interrupt_flag a := a.(sync_interrupt_flag).

Definition set_sync_interrupt_flag a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 v a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  end.

Definition get_current_mf a := a.(current_mf).

Definition set_current_mf a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 v a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  end.

Definition get_last_mf a := a.(last_mf).

Definition set_last_mf a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 v a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  end.

Definition get_current_sf a := a.(current_sf).

Definition set_current_sf a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 v a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  end.

Definition get_last_sf a := a.(last_sf).

Definition set_last_sf a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 a6 v a8 a9 a10 a11 a12 a13 a14 a15 a16
  end.

Definition get_standup_stack a := a.(standup_stack).

Definition set_standup_stack a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 a6 a7 v a9 a10 a11 a12 a13 a14 a15 a16
  end.

Definition get_standup_thread_data a := a.(standup_thread_data).

Definition set_standup_thread_data a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 v a10 a11 a12 a13 a14 a15 a16
  end.

Definition get_standup_thread_handle a := a.(standup_thread_handle).

Definition set_standup_thread_handle a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v a11 a12 a13 a14 a15 a16
  end.

Definition get_standup_flag a := a.(standup_flag).

Definition set_standup_flag a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 v a12 a13 a14 a15 a16
  end.

Definition get_standup_counter_handle a := a.(standup_counter_handle).

Definition set_standup_counter_handle a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 v a13 a14 a15 a16
  end.

Definition get_standup_alarm_count a := a.(standup_alarm_count).

Definition set_standup_alarm_count a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 v a14 a15 a16
  end.

Definition get_standup_alarm_object a := a.(standup_alarm_object).

Definition set_standup_alarm_object a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 v a15 a16
  end.

Definition get_standup_alarm_handle a := a.(standup_alarm_handle).

Definition set_standup_alarm_handle a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 v a16
  end.

Definition get_md_notime a := a.(md_notime).

Definition set_md_notime a v :=
  match a with
      mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
      => mkIntr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v
  end.

(***************************** Init ****************************)

Record Init := mkInit{
                   header : Header_Module.Header;
                   mvb_control : Control_Module.Mvb_Control;
                   mvb_administrator : Admin_Module.MVB_Administrator;
                   ports_Configuration : Ports_Configuration;
                   md_control : Md_Module.Md_Control;
                   function_directory : Function_Directory;
                   mvb_device_status : MVB_DEVICE_STATUS;

                   (* represent the same thing as mvb_device_status
                    * Just ignore it.
                    *)
                   mvb_device_status_16 : cyg_uint16;
                   MVB_CONTROL_FLAG : bool; (* should be unsigned short *)
                   MVB_ADMINISTRATOR_FLAG : bool; (* should be unsigned short *)
                   PORTS_CONFIGURATION_FLAG : bool; (* should be unsigned short *)
                   MD_CONTROL_FLAG : bool; (* should be unsigned short *)
                   FUNCTION_DIRECTORY_FLAG : bool; (* should be unsigned short *)
                   this_akey : nat; (* should be unsigned short *)
                   this_addr : nat
                 }.

Definition get_header a := a.(header).

Definition set_header a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_mvb_control a := a.(mvb_control).

Definition set_mvb_control a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 v a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_mvb_administrator a := a.(mvb_administrator).

Definition set_mvb_administrator a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 v a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_ports_Configuration a := a.(ports_Configuration).

Definition set_ports_Configuration a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 v a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_md_control a := a.(md_control).

Definition set_md_control a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 v a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_function_directory a := a.(function_directory).

Definition set_function_directory a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 a4 v a6 a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_mvb_device_status a := a.(mvb_device_status).

Definition set_mvb_device_status a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 a4 a5 v a7 a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_mvb_device_status_16 a := a.(mvb_device_status_16).

Definition set_mvb_device_status_16 a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 a4 a5 a6 v a8 a9 a10 a11 a12 a13 a14
  end.

Definition get_MVB_CONTROL_FLAG a := a.(MVB_CONTROL_FLAG).

Definition set_MVB_CONTROL_FLAG a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 a4 a5 a6 a7 v a9 a10 a11 a12 a13 a14
  end.

Definition get_MVB_ADMINISTRATOR_FLAG a := a.(MVB_ADMINISTRATOR_FLAG).

Definition set_MVB_ADMINISTRATOR_FLAG a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 v a10 a11 a12 a13 a14
  end.

Definition get_PORTS_CONFIGURATION_FLAG a := a.(PORTS_CONFIGURATION_FLAG).

Definition set_PORTS_CONFIGURATION_FLAG a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v a11 a12 a13 a14
  end.

Definition get_MD_CONTROL_FLAG a := a.(MD_CONTROL_FLAG).

Definition set_MD_CONTROL_FLAG a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 v a12 a13 a14
  end.

Definition get_FUNCTION_DIRECTORY_FLAG a := a.(FUNCTION_DIRECTORY_FLAG).

Definition set_FUNCTION_DIRECTORY_FLAG a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 v a13 a14
  end.

Definition get_this_akey a := a.(this_akey).

Definition set_this_akey a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 v a14
  end.

Definition get_this_addr a := a.(this_addr).

Definition set_this_addr a v :=
  match a with
      mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      => mkInit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 v
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

Definition get_exti_stack a := a.(exti_stack).

Definition set_exti_stack a v :=
  match a with
      mkMain a0 a1 a2 a3 a4 a5 a6 a7 a8
      => mkMain v a1 a2 a3 a4 a5 a6 a7 a8
  end.

Definition get_start_stack a := a.(start_stack).

Definition set_start_stack a v :=
  match a with
      mkMain a0 a1 a2 a3 a4 a5 a6 a7 a8
      => mkMain a0 v a2 a3 a4 a5 a6 a7 a8
  end.

Definition get_start_thread_data a := a.(start_thread_data).

Definition set_start_thread_data a v :=
  match a with
      mkMain a0 a1 a2 a3 a4 a5 a6 a7 a8
      => mkMain a0 a1 v a3 a4 a5 a6 a7 a8
  end.

Definition get_exti_thread_data a := a.(exti_thread_data).

Definition set_exti_thread_data a v :=
  match a with
      mkMain a0 a1 a2 a3 a4 a5 a6 a7 a8
      => mkMain a0 a1 a2 v a4 a5 a6 a7 a8
  end.

Definition get_start_thread_handle a := a.(start_thread_handle).

Definition set_start_thread_handle a v :=
  match a with
      mkMain a0 a1 a2 a3 a4 a5 a6 a7 a8
      => mkMain a0 a1 a2 a3 v a5 a6 a7 a8
  end.

Definition get_exti_thread_handle a := a.(exti_thread_handle).

Definition set_exti_thread_handle a v :=
  match a with
      mkMain a0 a1 a2 a3 a4 a5 a6 a7 a8
      => mkMain a0 a1 a2 a3 a4 v a6 a7 a8
  end.

Definition get_led_stack a := a.(led_stack).

Definition set_led_stack a v :=
  match a with
      mkMain a0 a1 a2 a3 a4 a5 a6 a7 a8
      => mkMain a0 a1 a2 a3 a4 a5 v a7 a8
  end.

Definition get_led_thread_data a := a.(led_thread_data).

Definition set_led_thread_data a v :=
  match a with
      mkMain a0 a1 a2 a3 a4 a5 a6 a7 a8
      => mkMain a0 a1 a2 a3 a4 a5 a6 v a8
  end.

Definition get_led_thread_handle a := a.(led_thread_handle).

Definition set_led_thread_handle a v :=
  match a with
      mkMain a0 a1 a2 a3 a4 a5 a6 a7 a8
      => mkMain a0 a1 a2 a3 a4 a5 a6 a7 v
  end.

(* Stupid constants needed *)
Definition CYGNUM_HAL_INTERRUPT_EXTI7 := 0.
Definition CYGNUM_HAL_INTERRUPT_EXTI8 := 1.
Definition CYGNUM_HAL_INTERRUPT_EXTI9 := 2.
Definition CYGNUM_HAL_INTERRUPT_EXTI10 := 3.
Definition CYGNUM_HAL_INTERRUPT_EXTI11 := 4.
Definition CYGNUM_HAL_INTERRUPT_EXTI12 := 5.
Definition CYGNUM_HAL_INTERRUPT_EXTI13 := 6.
Definition CYGNUM_HAL_INTERRUPT_EXTI14 := 7.

Definition EXTI_MAIN_FRAME_VECTOR := CYGNUM_HAL_INTERRUPT_EXTI7.
Definition EXTI_SLAVE_FRAME_VECTOR := CYGNUM_HAL_INTERRUPT_EXTI8.
Definition EXTI_SUPERVISORY_INT_VECTOR := CYGNUM_HAL_INTERRUPT_EXTI10.
Definition EXTI_SYNC_VECTOR := CYGNUM_HAL_INTERRUPT_EXTI11.
Definition EXIT_NO_TIME_VECTOR := CYGNUM_HAL_INTERRUPT_EXTI12.
Definition EXTI_TIMEOUT_VECTOR := CYGNUM_HAL_INTERRUPT_EXTI13.
Definition EXTI_ERROR_FRAME_VECTOR := CYGNUM_HAL_INTERRUPT_EXTI14.

Definition CYG_ISR_HANDLED := 1.
Definition CYG_ISR_CALL_DSR := 2.

Definition natToBITSET16 (n : nat) : BITSET16.
  Admitted.

Definition beq_UNSIGNED16 (n m : UNSIGNED16) : bool.
  Admitted.

Definition natToUNSIGNED16 (n : nat) : UNSIGNED16.
  Admitted.

Definition UNSIGNED16ToNat (n : UNSIGNED16) : nat.
  Admitted.

Definition FRAME_F_CODE (n : UNSIGNED16) : FRAME_F_CODE_CONST.
  Admitted.

Definition FRAME_ADDRESS (frame : UNSIGNED16) : UNSIGNED16.
Admitted.

Definition F_CODEToUNSIGNED8 (n : FRAME_F_CODE_CONST) : UNSIGNED8.
  Admitted.