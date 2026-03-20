---------------------------------- MODULE Tx -----------------------------------
EXTENDS Sequences, Integers, TLC

CONSTANTS Key, NoVal, BlockSize

Storage == [k \in Key |-> 0]

VARIABLE mem \* multi-version memory

INSTANCE Mem WITH
    \* assume value starts at 0 and each tx increase the value at most by 1,
    \* so the value should never exceed BlockSize.
    Val <- 0..BlockSize

ASSUME BlockSize > 0

Storage == [k \in Key |-> 0]

(* All possible transactions:
   - reads  : subset of Keys
   - writes : subset of Keys
   - deps   : function from each written key to a subset of reads
*)
Transactions ==
  UNION { { [ reads  |-> r,
              writes |-> w,
              deps   |-> d ] : d \in [ w -> SUBSET r ] } :
          r \in SUBSET Key, w \in SUBSET Key }

Blocks == [ 1..BlockSize -> Transactions ]

VARIABLES
    block, \* the block of transactions
    execStatus, \* execution status of transactions
    incarnation, \* incarnation numbers of transactions
    readSet \* the read set of transactions, used for validation

vars == << block, mem, execStatus, incarnation, readSet >>

ExecStatus == {
    "ReadyToExecute", \* ok to execute
    "Executed" \* ok to validate
}

TypeOK ==
    /\ block \in Blocks
    /\ TypeOKMem
    /\ execStatus \in [TxIndex -> ExecStatus]
    /\ incarnation \in [TxIndex -> Nat]
    /\ readSet \in [TxIndex -> Overlay]

(* Recursive sum over a finite set S of the values f(x) *)
RECURSIVE Sum(_, _)
Sum(S, st) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN st[x] + Sum(S \ {x}, st)

\* compute the write values of a transaction based on its dependencies and the current state
TxWriteSet(tx, st) == [k \in tx.writes |-> Sum(tx.deps[k], st)]

\* execute tx logic
ExecuteTx(txn) ==
    LET tx == block[txn]
        state == ViewMem(txn)
        reads == [k \in tx.reads |-> state[k]]
        writes == TxWriteSet(tx, state)
    IN
        /\ WriteMem(txn, writes)
        /\ readSet' = [readSet EXCEPT ![txn] = reads]

ValidateTx(txn) == \A k \in block[txn].reads: ReadMem(k, txn) = readSet[txn][k]

TxExecute(txn) ==
    /\ execStatus[txn] = "ReadyToExecute"
    /\ execStatus' = [execStatus EXCEPT ![txn] = "Executed"]
    /\ ExecuteTx(txn)
    /\ UNCHANGED << block, incarnation >>

TxValidateAbort(txn) ==
    /\ execStatus[txn] = "Executed"
    /\ ~ValidateTx(txn)
    /\ execStatus' = [execStatus EXCEPT ![txn] = "ReadyToExecute"]
    /\ incarnation' = [incarnation EXCEPT ![txn] = @ + 1]
    /\ mem' = [mem EXCEPT ![txn] = <<>>]
    /\ UNCHANGED << block, readSet >>

\* the committed states when transactions are executed sequentially
SeqStates[i \in 0..BlockSize] ==
    IF i = 0 THEN Storage
    ELSE LET tx == block[i]
             state == SeqStates[i - 1]
             writes == TxWriteSet(tx, state)
         IN
             ApplyChanges(state, writes)

\* executed and validated successfully, prerequisite for commit
CleanExecuted(txn) == execStatus[txn] = "Executed" /\ ValidateTx(txn)

\* transaction commitment is defined as a whole prefix of transactions are executed and validated successfully.
\* 0 is always committed as the base case.
Committed[txn \in 0..BlockSize] ==
    IF txn = 0 THEN TRUE
    ELSE Committed[txn - 1] /\ CleanExecuted(txn)

\* the largest committed transaction index, 0 if no transaction is committed.
CommittedTxn == CHOOSE txn \in 0..BlockSize:
    /\ Committed[txn]
    /\ txn = BlockSize \/ ~Committed[txn + 1]

\* compare the state of a transaction against the sequential execution state.
ConsistentState(txn) == ViewMem(txn + 1) = SeqStates[txn]

\* all txs are committed eventually
EventuallyCommitted == <>[]Committed[BlockSize]

\* Failed validation leads to re-execution
FailedValidationIncreaseIncarnation ==
    LET txn == BlockSize IN  \* only check one transaction for simplicity, but it can be generalized to all transactions.
    \* \A txn \in 1..BlockSize:
        \A n \in 0..10:
            incarnation[txn] = n /\ execStatus[txn]="Executed" /\ ~ValidateTx(txn) ~> execStatus[txn]="Executed" /\ incarnation[txn] > n

Properties ==
    /\ EventuallyCommitted
    /\ []ConsistentState(CommittedTxn)
    /\ FailedValidationIncreaseIncarnation

Init ==
    /\ block \in Blocks
    /\ InitMem
    /\ execStatus = [i \in TxIndex |-> "ReadyToExecute"]
    /\ incarnation = [i \in TxIndex |-> 0]
    /\ readSet = [i \in TxIndex |-> <<>>]

Next ==
    \/ Committed[BlockSize] /\ UNCHANGED vars
    \/ \E txn \in TxIndex: TxExecute(txn)
    \/ \E txn \in TxIndex: TxValidateAbort(txn)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

================================================================================
