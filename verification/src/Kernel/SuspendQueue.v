Inductive SuspendQueue :=
|mutex : nat -> SuspendQueue
|semaphore : nat -> SuspendQueue
|NULL : SuspendQueue. (*not in the above two, in run queue or alone, depending on the state of the thread*)
