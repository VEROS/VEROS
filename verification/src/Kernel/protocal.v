Set Implicit Arguments.



Parameter ThreadQueue : Set.

Inductive ThreadState : Set :=
| RUNNING : ThreadState
| SLEEPING : ThreadState
| COUNTSLEEP : ThreadState
| SUSPENDED : ThreadState
| CREATING : ThreadState
| EXITED : ThreadState.

Inductive Reason : Set :=
| NONE : Reason
| WAIT : Reason
| DELAY : Reason
| TIMEOUT : Reason
| BREAK : Reason
| DESTRUCT : Reason
| EXIT : Reason
| DONE : Reason.



Record Thread := mkthread{

  

  (*Inherited from SchedThread*)
  queue : ThreadQueue;

  mutex_count : nat;
  (*CYGSEM_KERNEL_SYNCH_MUTEX_PRIORITY_INVERSION_PROTOCOL is on*)

  original_priority : nat;
  priority_inherited : bool;


 (*Inhabited in Thread itself*)
  unique_id : nat;
 
  state : ThreadState;

  supend_count : nat;
  wakeup_count : nat;

  wait_info : nat;

  sleep_reason : Reason;
  wake_reason : Reason;

  (*Inherited from SchedThread_Implementation*)
  priority : nat;
  timeslice_count : nat;
  timeslice_enabled : bool

  (*TODO : duel direct list, add pred + next*)

}.


(*Need to add a check function : check this*)