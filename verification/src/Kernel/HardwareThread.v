Set Implicit Arguments.

Definition thread_entry := nat.

Definition ADDRESS := nat.

Record HardwareThread := mkHT {
  stack_base : ADDRESS;
  stack_size : nat;

  stack_limit : ADDRESS;

  stack_ptr : ADDRESS;
  
  entry_point : thread_entry;

  entry_data : ADDRESS

  (*HAL_SavedRegisters*)
}.

