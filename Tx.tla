---------------------------------- MODULE Tx -----------------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets

CONSTANTS Key, NoVal, BlockSize

Storage == [k \in Key |-> 0]

\* According to emulated transaction logic, max value is the iteration result of function `x |-> len(Key) * x + 1` on top of tx list.
MaxValue ==
    LET k == Cardinality(Key) IN
    IF k = 1
        THEN BlockSize
    ELSE
        (k ^ BlockSize - 1) \div (k - 1)

MaxIncarnation == 2^BlockSize - 1

VARIABLE mem \* multi-version memory

INSTANCE Mem WITH
    \* assume value starts at 0 and each tx increase the value at most by 1,
    \* so the value should never exceed BlockSize.
    Val <- 0..MaxValue

ASSUME BlockSize > 0

(* Transactions are modeled as relationships between arbitrary readset and writeset:
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
    readSet, \* the read set of transactions, used for validation
    commit_idx \* the next transaction to commit

vars == << block, mem, execStatus, incarnation, readSet, commit_idx >>

ExecStatus == {
    "ReadyToExecute", \* ok to execute
    "Executed" \* ok to validate
}

TypeOK ==
    /\ block \in Blocks
    /\ TypeOKMem
    /\ execStatus \in [TxIndex -> ExecStatus]
    /\ incarnation \in [TxIndex -> 0..MaxIncarnation] \* biggest incarnation is exponential in BlockSize in worst case.
    /\ readSet \in [TxIndex -> Overlay]
    /\ commit_idx \in 1..(BlockSize + 1)

(* Recursive sum over a finite set S of the values f(x) *)
RECURSIVE Sum(_, _)
Sum(S, st) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
             v == st[x] + Sum(S \ {x}, st)
         IN v % (MaxValue + 1)

\* compute the write values of a transaction based on its dependencies and the readset
TxWriteSet(tx, st) == [k \in tx.writes |-> Sum(tx.deps[k], st) + 1]

\* execute tx logic
ExecuteTx(txn) ==
    LET tx == block[txn]
        reads == [k \in tx.reads |-> ReadMem(k, txn)]
        writes == TxWriteSet(tx, reads)
    IN
        /\ WriteMem(txn, writes)
        /\ readSet' = [readSet EXCEPT ![txn] = reads]

ValidateTx(txn) == ValidateReadSet(readSet[txn], txn)

\* executed and validated successfully, prerequisite for commit
CleanExecuted(txn) == execStatus[txn] = "Executed" /\ ValidateTx(txn)

TxExecute(txn) ==
    /\ execStatus[txn] = "ReadyToExecute"
    /\ execStatus' = [execStatus EXCEPT ![txn] = "Executed"]
    /\ ExecuteTx(txn)
    /\ UNCHANGED << block, incarnation, commit_idx >>

TxValidateAbort(txn) ==
    /\ execStatus[txn] = "Executed"
    /\ ~ValidateTx(txn)
    /\ execStatus' = [execStatus EXCEPT ![txn] = "ReadyToExecute"]
    /\ incarnation' = [incarnation EXCEPT ![txn] = @ + 1]
    /\ mem' = [mem EXCEPT ![txn] = <<>>]
    /\ UNCHANGED << block, readSet, commit_idx >>

TryCommit(txn) ==
    /\ txn = commit_idx
    /\ commit_idx <= BlockSize
    /\ CleanExecuted(txn)
    /\ commit_idx' = txn + 1
    /\ UNCHANGED << block, mem, execStatus, incarnation, readSet >>

Init ==
    /\ InitMem
    /\ block \in Blocks
    /\ execStatus = [i \in TxIndex |-> "ReadyToExecute"]
    /\ incarnation = [i \in TxIndex |-> 0]
    /\ readSet = [i \in TxIndex |-> <<>>]
    /\ commit_idx = 1

Next ==
    \/ commit_idx = BlockSize + 1 /\ UNCHANGED vars
    \/ \E txn \in TxIndex: TxExecute(txn)
    \/ \E txn \in TxIndex: TxValidateAbort(txn)
    \/ \E txn \in {commit_idx} \cap TxIndex: TryCommit(txn)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Properties

\* the committed states when transactions are executed sequentially
SeqStates[i \in 0..BlockSize] ==
    IF i = 0 THEN Storage
    ELSE LET tx == block[i]
             state == SeqStates[i - 1]
             writes == TxWriteSet(tx, state)
         IN
             ApplyChanges(state, writes)

\* committed state is the same as sequentially execution.
ConsistentState ==
    \/ commit_idx = 1
    \/ LET committed == commit_idx - 1
      IN /\ CleanExecuted(committed)
         /\ ViewMem(committed + 1) = SeqStates[committed]

\* Failed validation leads to re-execution
FailedValidationIncreaseIncarnation ==
    LET txn == BlockSize IN  \* only check one transaction for simplicity, but it can be generalized to all transactions.
    \* \A txn \in 1..BlockSize:
        \A n \in 0..10:
            incarnation[txn] = n /\ execStatus[txn]="Executed" /\ ~ValidateTx(txn) ~> execStatus[txn]="Executed" /\ incarnation[txn] > n

Properties ==
    /\ <>[](commit_idx = BlockSize + 1)
    /\ []ConsistentState
    \* /\ FailedValidationIncreaseIncarnation

Symmetry == Permutations(Key)

================================================================================
