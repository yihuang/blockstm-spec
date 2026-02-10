---------------------------------- MODULE Tx -----------------------------------
EXTENDS Sequences, TLC

CONSTANTS Key, Val, NoVal, BlockSize, Storage

INSTANCE Mem

ASSUME BlockSize > 0
ASSUME Storage \in Dict
ASSUME Val \subseteq Nat

(* Tx is modeled as a function from read set to write set,
 * and assume all the txs in the block follow the same logic.
 *)
Tx(reads) == [k \in DOMAIN reads |-> reads[k] + 1]

VARIABLES
    mem, \* multi-version memory
    execStatus, \* execution status of transactions
    incarnation, \* incarnation numbers of transactions
    readSet \* the read set of transactions, used for validation

vars == << mem, execStatus, incarnation, readSet >>

ExecStatus == {
    "ReadyToExecute", \* ok to execute
    "Executed", \* ok to validate
    "Aborting" \* failed validation, ok to re-execute
}

TypeOK ==
    /\ TypeOKMem(mem)
    /\ execStatus \in [TxIndex -> ExecStatus]
    /\ incarnation \in [TxIndex -> Nat]
    /\ readSet \in [TxIndex -> Dict]

\* execute tx logic
ExecuteTx(txn) ==
    LET reads == ViewMem(mem, Storage, txn)
        writes == Tx(reads)
    IN
        /\ mem' = WriteMem(mem, txn, writes)
        /\ readSet' = [readSet EXCEPT ![txn] = reads]

TxExecute(txn) ==
    /\ execStatus[txn] = "ReadyToExecute"
    /\ execStatus' = [execStatus EXCEPT ![txn] = "Executed"]
    /\ ExecuteTx(txn)
    /\ UNCHANGED incarnation

TxValidateOK(txn) ==
    /\ execStatus[txn] = "Executed"
    /\ ViewMem(mem, Storage, txn) = readSet[txn]
    /\ UNCHANGED << mem, execStatus, incarnation, readSet >>

TxValidateAbort(txn) ==
    /\ execStatus[txn] = "Executed"
    /\ execStatus' = [execStatus EXCEPT ![txn] = "Aborting"]
    /\ ViewMem(mem, Storage, txn) /= readSet[txn]
    /\ UNCHANGED << mem, incarnation, readSet >>

TxReexecute(txn) ==
    /\ execStatus[txn] = "Aborting"
    /\ execStatus' = [execStatus EXCEPT ![txn] = "Executed"]
    /\ ExecuteTx(txn)
    /\ incarnation' = [incarnation EXCEPT ![txn] = @ + 1]

Init ==
    /\ mem = EmptyMem
    /\ execStatus = [i \in TxIndex |-> "ReadyToExecute"]
    /\ incarnation = [i \in TxIndex |-> 0]
    /\ readSet = [i \in TxIndex |-> <<>>]

ApplyTx(st) == ApplyOverlay(st, Tx(st))

(* the final state when transactions are executed sequentially *)
SeqState ==
    LET iter[i \in 0..BlockSize] ==
        IF i = 0 THEN Storage
        ELSE ApplyTx(iter[i - 1])
    IN iter[BlockSize]

AllDone ==
    /\ \A txn \in TxIndex: execStatus[txn] = "Executed"
    /\ ViewMem(mem, Storage, (BlockSize+1)) = SeqState

Liveness == <>[]AllDone

Next ==
    \E txn \in TxIndex:
        TxExecute(txn) \/ TxValidateOK(txn) \/ TxValidateAbort(txn) \/ TxReexecute(txn)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

================================================================================
