Set Implicit Arguments.

Definition BITFIELD16 := nat.

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

