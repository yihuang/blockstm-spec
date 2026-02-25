---------------------------------- MODULE TxCancel -----------------------------------
EXTENDS Sequences, Integers, TLC

CONSTANTS Key, Val, NoVal, BlockSize
CONSTANTS K

INSTANCE Mem

ASSUME K \in Key
ASSUME BlockSize >= 2

Tx2 == 2

(* Cancellation should clear ESTIMATE marks for all txns.
 * Otherwise a woken txn can immediately block again.
 *)

ExecStatus == {
    "ReadyToExecute", \* ok to execute
    "Executed", \* done
    "Aborting" \* unused in this model
}

VARIABLES
    mem, \* multi-version memory
    est, \* estimate marks per txn: set of keys marked ESTIMATE
    execStatus, \* execution status of transactions
    dep \* per-txn blocker index when waiting, 0 otherwise

vars == << mem, est, execStatus, dep >>

TypeOK ==
    /\ TypeOKMem(mem)
    /\ est \in [TxIndex -> SUBSET Key]
    /\ execStatus \in [TxIndex -> ExecStatus]
    /\ dep \in [TxIndex -> (TxIndex \cup {0})]

EstimateBlocker(txn, key) ==
    LET cs == {i \in TxIndex: i < txn /\ key \in est[i]}
    IN IF cs = {} THEN 0 ELSE Max(cs)

\* A read attempt by txn that may block on an ESTIMATE mark.
ReadStep(txn) ==
    LET b == EstimateBlocker(txn, K)
    IN
        /\ execStatus[txn] = "ReadyToExecute"
        /\ dep[txn] = 0
        /\ IF b = 0
              THEN /\ execStatus' = [execStatus EXCEPT ![txn] = "Executed"]
                   /\ dep' = [dep EXCEPT ![txn] = 0]
              ELSE /\ execStatus' = execStatus
                   /\ dep' = [dep EXCEPT ![txn] = b]
        /\ UNCHANGED << mem, est >>

\* CancelAll wakes waiting txns and clears ESTIMATE marks.
CancelAll ==
    /\ \E i \in TxIndex: dep[i] # 0
    /\ execStatus' = execStatus
    /\ dep' = [i \in TxIndex |-> 0]
    /\ est' = [i \in TxIndex |-> {}]
    /\ UNCHANGED mem

Init ==
    /\ mem = EmptyMem
    /\ est = [i \in TxIndex |-> IF i = 1 THEN {K} ELSE {}]
    /\ execStatus = [i \in TxIndex |-> "ReadyToExecute"]
    /\ dep = [i \in TxIndex |-> 0]

Next ==
    ReadStep(Tx2) \/ CancelAll \/ UNCHANGED vars

Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(CancelAll)
        /\ WF_vars(ReadStep(Tx2))

LiveDone == <> (execStatus[Tx2] = "Executed")

================================================================================
