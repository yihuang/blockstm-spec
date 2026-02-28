---------------------------------- MODULE Tx -----------------------------------
EXTENDS Sequences, Integers, TLC

CONSTANTS Key, NoVal, BlockSize

INSTANCE Mem WITH
    \* assume value starts at 0 and each tx increase the value at most by 1,
    \* so the value should never exceed BlockSize.
    Val <- 0..BlockSize

ASSUME BlockSize > 0

Storage == [k \in Key |-> 0]

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
    /\ readSet \in [TxIndex -> Overlay]

\* execute tx logic
ExecuteTx(txn) ==
    LET reads == ViewMem(mem, Storage, txn)
        writes == Tx(reads)
    IN
        /\ mem' = WriteMem(mem, txn, writes)
        /\ readSet' = [readSet EXCEPT ![txn] = reads]

ValidateTx(txn) == ViewMem(mem, Storage, txn) = readSet[txn]

TxFirstExecute(txn) ==
    /\ execStatus[txn] = "ReadyToExecute"
    /\ execStatus' = [execStatus EXCEPT ![txn] = "Executed"]
    /\ ExecuteTx(txn)
    /\ UNCHANGED incarnation

TxReexecute(txn) ==
    /\ execStatus[txn] = "Aborting"
    /\ execStatus' = [execStatus EXCEPT ![txn] = "Executed"]
    /\ ExecuteTx(txn)
    /\ incarnation' = [incarnation EXCEPT ![txn] = @ + 1]

TxExecute(txn) ==
    /\ TxFirstExecute(txn) \/ TxReexecute(txn)

TxValidateOK(txn) ==
    /\ execStatus[txn] = "Executed"
    /\ ValidateTx(txn)
    /\ UNCHANGED << mem, execStatus, incarnation, readSet >>

TxValidateAbort(txn) ==
    /\ execStatus[txn] = "Executed"
    /\ ~ValidateTx(txn)
    /\ execStatus' = [execStatus EXCEPT ![txn] = "Aborting"]
    /\ UNCHANGED << mem, incarnation, readSet >>

TxValidate(txn) == TxValidateOK(txn) \/ TxValidateAbort(txn)

ApplyTx(st) == ApplyChanges(st, Tx(st))

\* the committed state when transactions are executed sequentially
SeqState(txn) ==
    LET iter[i \in 0..BlockSize] ==
        IF i = 0 THEN Storage
        ELSE ApplyTx(iter[i - 1])
    IN iter[txn]

\* executed and validated successfully, prerequisite for commit
CleanExecuted(txn) == execStatus[txn] = "Executed" /\ ValidateTx(txn)

\* logical committed transaction index (all txs in 1..txn are clean executed, txn+1 is not executed or not clean executed), 0 if no committed txn
CommittedTxn == CHOOSE txn \in 0..BlockSize:
    \/ /\ txn = 0
      /\ ~CleanExecuted(1)
    \/ /\ \A i \in 1..txn: CleanExecuted(i)
      /\ (txn = BlockSize \/ ~CleanExecuted(txn + 1))

\* the state is consistent with sequential execution result after executing txn
ConsistentState(txn) == ViewMem(mem, Storage, txn+1) = SeqState(txn)

\* validate committed states
CommittedState == [](
    \A txn \in 1..CommittedTxn: ConsistentState(txn)
)

\* all txs are committed eventually
EventuallyCommitted == <>[](CommittedTxn = BlockSize)

Properties == EventuallyCommitted /\ CommittedState

Init ==
    /\ mem = EmptyMem
    /\ execStatus = [i \in TxIndex |-> "ReadyToExecute"]
    /\ incarnation = [i \in TxIndex |-> 0]
    /\ readSet = [i \in TxIndex |-> <<>>]

Next ==
    \/ \E txn \in TxIndex: TxExecute(txn)
    \/ \E txn \in TxIndex: TxValidate(txn)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

================================================================================
