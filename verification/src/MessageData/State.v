Set Implicit Arguments.

Add LoadPath "../Kernel".
Require MVB_def.

Record State := mkState{
                    message_data : MVB_def.Message_data;
                    ba_state : MVB_def.Ba;
                    intr : MVB_def.Intr;
                    init : MVB_def.Init;
                    main : MVB_def.Main
                  }.

Definition get_message_data a := a.(message_data).

Definition set_message_data a v :=
  match a with
      mkState a0 a1 a2 a3 a4
      => mkState v a1 a2 a3 a4
  end.

Definition get_ba_state a := a.(ba_state).

Definition set_ba_state a v :=
  match a with
      mkState a0 a1 a2 a3 a4
      => mkState a0 v a2 a3 a4
  end.

Definition get_intr a := a.(intr).

Definition set_intr a v :=
  match a with
      mkState a0 a1 a2 a3 a4
      => mkState a0 a1 v a3 a4
  end.

Definition get_init a := a.(init).

Definition set_init a v :=
  match a with
      mkState a0 a1 a2 a3 a4
      => mkState a0 a1 a2 v a4
  end.

Definition get_main a := a.(main).

Definition set_main a v :=
  match a with
      mkState a0 a1 a2 a3 a4
      => mkState a0 a1 a2 a3 v
  end.

(*************************** masks ****************************)

Definition get_current_index a := MVB_def.get_current_index a.(message_data).

Definition set_current_index a v :=
  set_message_data a (MVB_def.set_current_index a.(message_data) v).

(********************************** ba *************************************)

Definition get_bp_number a := MVB_def.get_bp_number a.(ba_state).

Definition set_bp_number a v :=
  set_ba_state a (MVB_def.set_bp_number a.(ba_state) v).

Definition get_ba_context a := MVB_def.get_ba_context a.(ba_state).

Definition set_ba_context a v :=
  set_ba_state a (MVB_def.set_ba_context a.(ba_state) v).

Definition get_ba_mf a := MVB_def.get_ba_mf a.(ba_state).

Definition set_ba_mf a v :=
  set_ba_state a (MVB_def.set_ba_mf a.(ba_state) v).

Definition get_device_scan_unit a := MVB_def.get_device_scan_unit a.(ba_state).

Definition set_device_scan_unit a v :=
  set_ba_state a (MVB_def.set_device_scan_unit a.(ba_state) v).

Definition get_ba_context_devices_scan_i a :=
  MVB_def.get_ba_context_devices_scan_i a.(ba_state).

Definition set_ba_context_devices_scan_i a v :=
  set_ba_state a (MVB_def.set_ba_context_devices_scan_i a.(ba_state) v).

Definition get_ba_context_devices_scan_j a :=
  MVB_def.get_ba_context_devices_scan_j a.(ba_state).

Definition set_ba_context_devices_scan_j a v :=
  set_ba_state a (MVB_def.set_ba_context_devices_scan_j a.(ba_state) v).

Definition get_ba_context_devices_scan_address a :=
  MVB_def.get_ba_context_devices_scan_address a.(ba_state).

Definition set_ba_context_devices_scan_address a v :=
  set_ba_state a (MVB_def.set_ba_context_devices_scan_address a.(ba_state) v).

Definition get_ba_context_mastership_transfer_address a :=
  MVB_def.get_ba_context_mastership_transfer_address a.(ba_state).

Definition set_ba_context_mastership_transfer_address a v :=
  set_ba_state a (MVB_def.set_ba_context_mastership_transfer_address a.(ba_state) v).

Definition get_ba_context_mastership_transfer_act a :=
  MVB_def.get_ba_context_mastership_transfer_act a.(ba_state).

Definition set_ba_context_mastership_transfer_act a v :=
  set_ba_state a (MVB_def.set_ba_context_mastership_transfer_act a.(ba_state) v).

Definition get_admin_obj a :=
  MVB_def.get_admin_obj a.(ba_state).

Definition set_admin_obj a v :=
  set_ba_state a (MVB_def.set_admin_obj a.(ba_state) v).

Definition get_devices_scan_strategy a :=
  MVB_def.get_devices_scan_strategy a.(ba_state).

Definition set_devices_scan_strategy a v :=
  set_ba_state a (MVB_def.set_devices_scan_strategy a.(ba_state) v).

Definition get_devices_list a := MVB_def.get_devices_list a.(ba_state).

Definition set_devices_list a v :=
  set_ba_state a (MVB_def.set_devices_list a.(ba_state) v).

Definition get_devices_list_timeout_count a :=
  MVB_def.get_devices_list_timeout_count a.(ba_state).

Definition set_devices_list_timeout_count a v :=
  set_ba_state a (MVB_def.set_devices_list_timeout_count a.(ba_state) v).

Definition get_md_ability_array a := MVB_def.get_md_ability_array a.(ba_state).

Definition set_md_ability_array a v :=
  set_ba_state a (MVB_def.set_md_ability_array a.(ba_state) v).

Definition get_md_ability_count a := MVB_def.get_md_ability_count a.(ba_state).

Definition set_md_ability_count a v :=
  set_ba_state a (MVB_def.set_md_ability_count a.(ba_state) v).

(******************************** Intr *************************************)

Definition get_wait_for_ba a := MVB_def.get_wait_for_ba a.(intr).

Definition set_wait_for_ba a v :=
  set_intr a (MVB_def.set_wait_for_ba a.(intr) v).

Definition get_frame_checkbit a := MVB_def.get_frame_checkbit a.(intr).

Definition set_frame_checkbit a v :=
  set_intr a (MVB_def.set_frame_checkbit a.(intr) v).

Definition get_sync_checkbit a := MVB_def.get_sync_checkbit a.(intr).

Definition set_sync_checkbit a v :=
  set_intr a (MVB_def.set_sync_checkbit a.(intr) v).

Definition get_sync_interrupt_flag a := MVB_def.get_sync_interrupt_flag a.(intr).

Definition set_sync_interrupt_flag a v :=
  set_intr a (MVB_def.set_sync_interrupt_flag a.(intr) v).

Definition get_current_mf a := MVB_def.get_current_mf a.(intr).

Definition set_current_mf a v :=
  set_intr a (MVB_def.set_current_mf a.(intr) v).

Definition get_last_mf a := MVB_def.get_last_mf a.(intr).

Definition set_last_mf a v :=
  set_intr a (MVB_def.set_last_mf a.(intr) v).

Definition get_current_sf a := MVB_def.get_current_sf a.(intr).

Definition set_current_sf a v :=
  set_intr a (MVB_def.set_current_sf a.(intr) v).

Definition get_last_sf a := MVB_def.get_last_sf a.(intr).

Definition set_last_sf a v :=
  set_intr a (MVB_def.set_last_sf a.(intr) v).

Definition get_standup_stack a := MVB_def.get_standup_stack a.(intr).

Definition set_standup_stack a v :=
  set_intr a (MVB_def.set_standup_stack a.(intr) v).

Definition get_standup_thread_data a := MVB_def.get_standup_thread_data a.(intr).

Definition set_standup_thread_data a v :=
  set_intr a (MVB_def.set_standup_thread_data a.(intr) v).

Definition get_standup_thread_handle a := MVB_def.get_standup_thread_handle a.(intr).

Definition set_standup_thread_handle a v :=
  set_intr a (MVB_def.set_standup_thread_handle a.(intr) v).

Definition get_standup_flag a := MVB_def.get_standup_flag a.(intr).

Definition set_standup_flag a v :=
  set_intr a (MVB_def.set_standup_flag a.(intr) v).

Definition get_standup_counter_handle a := MVB_def.get_standup_counter_handle a.(intr).

Definition set_standup_counter_handle a v :=
  set_intr a (MVB_def.set_standup_counter_handle a.(intr) v).

Definition get_standup_alarm_count a := MVB_def.get_standup_alarm_count a.(intr).

Definition set_standup_alarm_count a v :=
  set_intr a (MVB_def.set_standup_alarm_count a.(intr) v).

Definition get_standup_alarm_object a := MVB_def.get_standup_alarm_object a.(intr).

Definition set_standup_alarm_object a v :=
  set_intr a (MVB_def.set_standup_alarm_object a.(intr) v).

Definition get_standup_alarm_handle a := MVB_def.standup_alarm_handle a.(intr).

Definition set_standup_alarm_handle a v :=
  set_intr a (MVB_def.set_standup_alarm_handle a.(intr) v).

Definition get_md_notime a := MVB_def.get_md_notime a.(intr).

Definition set_md_notime a v :=
  set_intr a (MVB_def.set_md_notime a.(intr) v).

(***************************** Init ****************************)

Definition get_header a := MVB_def.get_header a.(init).

Definition set_header a v :=
  set_init a (MVB_def.set_header a.(init) v).

Definition get_mvb_control a := MVB_def.get_mvb_control a.(init).

Definition set_mvb_control a v :=
  set_init a (MVB_def.set_mvb_control a.(init) v).

Definition get_mvb_administrator a := MVB_def.get_mvb_administrator a.(init).

Definition set_mvb_administrator a v :=
  set_init a (MVB_def.set_mvb_administrator a.(init) v).

Definition get_ports_Configuration a := MVB_def.get_ports_Configuration a.(init).

Definition set_ports_Configuration a v :=
  set_init a (MVB_def.set_ports_Configuration a.(init) v).

Definition get_md_control a := MVB_def.get_md_control a.(init).

Definition set_md_control a v :=
  set_init a (MVB_def.set_md_control a.(init) v).

Definition get_function_directory a := MVB_def.get_function_directory a.(init).

Definition set_function_directory a v :=
  set_init a (MVB_def.set_function_directory a.(init) v).

Definition get_mvb_device_status a := MVB_def.get_mvb_device_status a.(init).

Definition set_mvb_device_status a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init) v).

Definition get_mvb_device_status_16 a := MVB_def.get_mvb_device_status_16 a.(init).

Definition set_mvb_device_status_16 a v :=
  set_init a (MVB_def.set_mvb_device_status_16 a.(init) v).

Definition get_MVB_CONTROL_FLAG a := MVB_def.get_MVB_CONTROL_FLAG a.(init).

Definition set_MVB_CONTROL_FLAG a v :=
  set_init a (MVB_def.set_MVB_CONTROL_FLAG a.(init) v).

Definition get_MVB_ADMINISTRATOR_FLAG a := MVB_def.get_MVB_ADMINISTRATOR_FLAG a.(init).

Definition set_MVB_ADMINISTRATOR_FLAG a v :=
  set_init a (MVB_def.set_MVB_ADMINISTRATOR_FLAG a.(init) v).

Definition get_PORTS_CONFIGURATION_FLAG a := MVB_def.get_PORTS_CONFIGURATION_FLAG a.(init).

Definition set_PORTS_CONFIGURATION_FLAG a v :=
  set_init a (MVB_def.set_PORTS_CONFIGURATION_FLAG a.(init) v).

Definition get_MD_CONTROL_FLAG a := MVB_def.get_MD_CONTROL_FLAG a.(init).

Definition set_MD_CONTROL_FLAG a v :=
  set_init a (MVB_def.set_MD_CONTROL_FLAG a.(init) v).

Definition get_FUNCTION_DIRECTORY_FLAG a := MVB_def.get_FUNCTION_DIRECTORY_FLAG a.(init).

Definition set_FUNCTION_DIRECTORY_FLAG a v :=
  set_init a (MVB_def.set_FUNCTION_DIRECTORY_FLAG a.(init) v).

Definition get_this_akey a := MVB_def.get_this_akey a.(init).

Definition set_this_akey a v :=
  set_init a (MVB_def.set_this_akey a.(init) v).

Definition get_this_addr a := MVB_def.get_this_addr a.(init).

Definition set_this_addr a v :=
  set_init a (MVB_def.set_this_addr a.(init) v).

Definition get_ser a := MVB_def.get_ser a.(init).(MVB_def.mvb_device_status).

Definition set_ser a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_ser a.(init).(MVB_def.mvb_device_status) v)).

Definition get_dnr a := MVB_def.get_dnr a.(init).(MVB_def.mvb_device_status).

Definition set_dnr a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_dnr a.(init).(MVB_def.mvb_device_status) v)).

Definition get_frc a := MVB_def.get_frc a.(init).(MVB_def.mvb_device_status).

Definition set_frc a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_frc a.(init).(MVB_def.mvb_device_status) v)).

Definition get_erd a := MVB_def.get_erd a.(init).(MVB_def.mvb_device_status).

Definition set_erd a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_erd a.(init).(MVB_def.mvb_device_status) v)).

Definition get_sdd a := MVB_def.get_sdd a.(init).(MVB_def.mvb_device_status).

Definition set_sdd a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_sdd a.(init).(MVB_def.mvb_device_status) v)).

Definition get_ssd a := MVB_def.get_ssd a.(init).(MVB_def.mvb_device_status).

Definition set_ssd a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_ssd a.(init).(MVB_def.mvb_device_status) v)).

Definition get_rld a := MVB_def.get_rld a.(init).(MVB_def.mvb_device_status).

Definition set_rld a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_rld a.(init).(MVB_def.mvb_device_status) v)).

Definition get_lat a := MVB_def.get_lat a.(init).(MVB_def.mvb_device_status).

Definition set_lat a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_lat a.(init).(MVB_def.mvb_device_status) v)).

Definition get_cs3 a := MVB_def.get_cs3 a.(init).(MVB_def.mvb_device_status).

Definition set_cs3 a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_cs3 a.(init).(MVB_def.mvb_device_status) v)).

Definition get_cs2 a := MVB_def.get_cs2 a.(init).(MVB_def.mvb_device_status).

Definition set_cs2 a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_cs2 a.(init).(MVB_def.mvb_device_status) v)).

Definition get_cs1 a := MVB_def.get_cs1 a.(init).(MVB_def.mvb_device_status).

Definition set_cs1 a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_cs1 a.(init).(MVB_def.mvb_device_status) v)).

Definition get_cs0 a := MVB_def.get_cs0 a.(init).(MVB_def.mvb_device_status).

Definition set_cs0 a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_cs0 a.(init).(MVB_def.mvb_device_status) v)).

Definition get_md a := MVB_def.get_md a.(init).(MVB_def.mvb_device_status).

Definition set_md a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_md a.(init).(MVB_def.mvb_device_status) v)).

Definition get_gw a := MVB_def.get_gw a.(init).(MVB_def.mvb_device_status).

Definition set_gw a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_gw a.(init).(MVB_def.mvb_device_status) v)).

Definition get_ba a := MVB_def.get_ba a.(init).(MVB_def.mvb_device_status).

Definition set_ba a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_ba a.(init).(MVB_def.mvb_device_status) v)).

Definition get_sp a := MVB_def.get_sp a.(init).(MVB_def.mvb_device_status).

Definition set_sp a v :=
  set_init a (MVB_def.set_mvb_device_status a.(init)
               (MVB_def.set_sp a.(init).(MVB_def.mvb_device_status) v)).

(******************************* Main ********************************)

Definition get_exti_stack a := MVB_def.get_exti_stack a.(main).

Definition set_exti_stack a v :=
  set_main a (MVB_def.set_exti_stack a.(main) v).

Definition get_start_stack a := MVB_def.get_start_stack a.(main).

Definition set_start_stack a v :=
  set_main a (MVB_def.set_start_stack a.(main) v).

Definition get_start_thread_data a := MVB_def.get_start_thread_data a.(main).

Definition set_start_thread_data a v :=
  set_main a (MVB_def.set_start_thread_data a.(main) v).

Definition get_exti_thread_data a := MVB_def.get_exti_thread_data a.(main).

Definition set_exti_thread_data a v :=
  set_main a (MVB_def.set_exti_thread_data a.(main) v).

Definition get_start_thread_handle a := MVB_def.get_start_thread_handle a.(main).

Definition set_start_thread_handle a v :=
  set_main a (MVB_def.set_start_thread_handle a.(main) v).

Definition get_exti_thread_handle a := MVB_def.get_exti_thread_handle a.(main).

Definition set_exti_thread_handle a v :=
  set_main a (MVB_def.set_exti_thread_handle a.(main) v).

Definition get_led_stack a := MVB_def.get_led_stack a.(main).

Definition set_led_stack a v :=
  set_main a (MVB_def.set_led_stack a.(main) v).

Definition get_led_thread_data a := MVB_def.get_led_thread_data a.(main).

Definition set_led_thread_data a v :=
  set_main a (MVB_def.set_led_thread_data a.(main) v).

Definition get_led_thread_handle a := MVB_def.get_led_thread_handle a.(main).

Definition set_led_thread_handle a v :=
  set_main a (MVB_def.set_led_thread_handle a.(main) v).
