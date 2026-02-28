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

TxExecute(txn) ==
    /\ execStatus[txn] = "ReadyToExecute"
    /\ execStatus' = [execStatus EXCEPT ![txn] = "Executed"]
    /\ ExecuteTx(txn)
    /\ UNCHANGED incarnation

TxValidateAbort(txn) ==
    /\ execStatus[txn] = "Executed"
    /\ ~ValidateTx(txn)
    /\ execStatus' = [execStatus EXCEPT ![txn] = "ReadyToExecute"]
    /\ incarnation' = [incarnation EXCEPT ![txn] = @ + 1]
    /\ UNCHANGED << mem, readSet >>

ApplyTx(st) == ApplyChanges(st, Tx(st))

\* the committed state when transactions are executed sequentially
SeqState(txn) ==
    LET iter[i \in 0..BlockSize] ==
        IF i = 0 THEN Storage
        ELSE ApplyTx(iter[i - 1])
    IN iter[txn]

\* executed and validated successfully, prerequisite for commit
CleanExecuted(txn) == execStatus[txn] = "Executed" /\ ValidateTx(txn)

\* transaction commitment is defined as a whole prefix of transactions are executed and validated successfully.
\* 0 is always committed as the base case, and out of range indics are never committed.
Committed(txn) ==
    \/ txn = 0
    \/ txn \in TxIndex /\ \A i \in 1..txn: CleanExecuted(i)

\* the largest committed transaction index, 0 if no transaction is committed.
CommittedTxn == CHOOSE txn \in 0..BlockSize:
    Committed(txn) /\ ~Committed(txn+1)

\* compare the state of a transaction against the sequential execution state.
ConsistentState(txn) == ViewMem(mem, Storage, txn+1) = SeqState(txn)

\* all txs are committed eventually
EventuallyCommitted == <>[](CommittedTxn = BlockSize)

Properties == EventuallyCommitted /\ []ConsistentState(CommittedTxn)

Init ==
    /\ mem = EmptyMem
    /\ execStatus = [i \in TxIndex |-> "ReadyToExecute"]
    /\ incarnation = [i \in TxIndex |-> 0]
    /\ readSet = [i \in TxIndex |-> <<>>]

Next ==
    \/ (\A txn \in TxIndex: CleanExecuted(txn)) /\ UNCHANGED vars
    \/ \E txn \in TxIndex: TxExecute(txn)
    \/ \E txn \in TxIndex: TxValidateAbort(txn)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

================================================================================
