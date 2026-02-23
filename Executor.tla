------------------------------- MODULE Executor --------------------------------
EXTENDS Integers, Sequences

CONSTANTS Key, Val, NoVal, BlockSize, Executors, NoTask

ASSUME Executors \in Nat

VARIABLES
    mem, \* multi-version memory
    execStatus, \* execution status of transactions
    incarnation, \* incarnation numbers of transactions
    readSet \* the read set of transactions, used for validation

Tx == INSTANCE Tx

VARIABLES
    \* global shared counters
    execution_idx, \* the next transaction to execute
    validation_idx, \* the next transaction to validate
    commit_idx, \* the next transaction to commit
    active_tasks, \* the number of currently active tasks
    validation_wave, \* validation wave counter, used to establish order of validation events

    \* executor local states
    tasks, \* the current task of each executor
    terminated, \* whether the executor is terminated

    \* tx validation status
    tx_validated_wave \* the biggest wave number when each transaction was validated succesfully

txVars == << mem, execStatus, incarnation, readSet >>
vars == << txVars, execution_idx, validation_idx, commit_idx, active_tasks, validation_wave, tasks, terminated, tx_validated_wave >>

Task == [
    txn: Tx!TxIndex ,
    kind: {"Execution", "Validation"}
]
\* NoTask == CHOOSE t: t \notin Task

TypeOK ==
    /\ Tx!TypeOK
    /\ execution_idx \in 1..(BlockSize + 1)
    /\ validation_idx \in 1..(BlockSize + 1)
    /\ commit_idx \in 1..(BlockSize + 1)
    /\ active_tasks \in 0..Executors
    /\ validation_wave \in Nat
    /\ tasks \in [1..Executors -> Task \union {NoTask}]
    /\ terminated \in [1..Executors -> BOOLEAN]
    /\ tx_validated_wave \in [1..BlockSize -> Nat]

Init ==
    /\ Tx!Init
    /\ execution_idx = 1
    /\ validation_idx = 1
    /\ commit_idx = 1
    /\ active_tasks = 0
    /\ validation_wave = 1  \* starts from 1, 0 is reserved for not validated status
    /\ tasks = [e \in 1..Executors |-> NoTask]
    /\ terminated = [e \in 1..Executors |-> FALSE]
    /\ tx_validated_wave = [txn \in 1..BlockSize |-> 0]

PreferValidation == validation_idx < execution_idx

NextTaskExecution(e) ==
    /\ ~PreferValidation
    /\ execution_idx < BlockSize + 1
    /\ execution_idx' = execution_idx + 1
    /\ tasks' = [tasks EXCEPT ![e] = [txn |-> execution_idx, kind |-> "Execution"]]
    /\ UNCHANGED << validation_idx >>

NextTaskValidation(e) ==
    /\ PreferValidation
    /\ validation_idx < BlockSize + 1
    /\ validation_idx' = validation_idx + 1
    /\ tasks' = [tasks EXCEPT ![e] = [txn |-> validation_idx, kind |-> "Validation"]]
    /\ UNCHANGED << execution_idx >>

FetchTask(e) ==
    /\ tasks[e] = NoTask
    /\ NextTaskExecution(e) \/ NextTaskValidation(e)
    /\ active_tasks' = active_tasks + 1
    /\ UNCHANGED << commit_idx, validation_wave, terminated, tx_validated_wave, txVars >>

ResetValidationIdx(txn) ==
    IF txn < validation_idx THEN
        /\ validation_idx' = txn
        /\ validation_wave' = validation_wave + 1
    ELSE
        UNCHANGED << validation_idx, validation_wave >>

SetTxValidatedWave(txn, wave) ==
    IF wave > tx_validated_wave[txn] THEN
        tx_validated_wave' = [tx_validated_wave EXCEPT ![txn] = wave]
    ELSE
        UNCHANGED tx_validated_wave

ExecuteTx(e) ==
    LET txn == tasks[e].txn IN
    /\ tasks[e].kind = "Execution"
    /\ Tx!TxExecute(txn)
    /\ IF txn < validation_idx THEN
         /\ tasks' = [tasks EXCEPT ![e] = [@ EXCEPT !.kind = "Validation"]]
         /\ IF incarnation[txn] = 0 THEN \* only write new key in first incarnation
             ResetValidationIdx(txn + 1)
           ELSE
             UNCHANGED << validation_idx, validation_wave >>
         /\ UNCHANGED << active_tasks >>
       ELSE
         /\ tasks' = [tasks EXCEPT ![e] = NoTask]
         /\ active_tasks' = active_tasks - 1
         /\ UNCHANGED << validation_idx, validation_wave >>
    /\ UNCHANGED << execution_idx, tx_validated_wave >>

ValidateTx(e) ==
    LET txn == tasks[e].txn IN
    /\ tasks[e].kind = "Validation"
    /\ IF ENABLED Tx!TxValidate(txn) THEN
        \/ Tx!TxValidateAbort(txn)
          /\ tasks' = [tasks EXCEPT ![e] = [@ EXCEPT !.kind = "Execution"]]
          /\ UNCHANGED << active_tasks, tx_validated_wave >>

        \/ Tx!TxValidateOK(txn)
          /\ tasks' = [tasks EXCEPT ![e] = NoTask]
          /\ active_tasks' = active_tasks - 1
          /\ SetTxValidatedWave(txn, validation_wave)
      ELSE
        /\ tasks' = [tasks EXCEPT ![e] = NoTask] \* skip if tx is not ready to validate
        /\ active_tasks' = active_tasks - 1
        /\ UNCHANGED << txVars, tx_validated_wave >>
    /\ UNCHANGED << execution_idx, validation_idx, validation_wave >>

ExecTask(e) ==
    /\ tasks[e] /= NoTask
    /\ ExecuteTx(e) \/ ValidateTx(e)
    /\ UNCHANGED << commit_idx, terminated >>

CheckDone(e) ==
    /\ ~terminated[e]
    /\ validation_idx = BlockSize + 1
    /\ execution_idx = BlockSize + 1
    /\ active_tasks = 0
    /\ terminated' = [terminated EXCEPT ![e] = TRUE]
    /\ UNCHANGED << execution_idx, validation_idx, commit_idx, validation_wave, tasks, active_tasks, tx_validated_wave, txVars >>

Done(e) ==
    /\ terminated[e]
    /\ UNCHANGED vars

Executor(e) ==
    CheckDone(e) \/ FetchTask(e) \/ ExecTask(e) \/ Done(e)

Next ==
    \E e \in 1..Executors:
        Executor(e)

\* Properties

\* Invariant: no two executors can execute the same transaction at the same time
NoConcurrentExecution ==
    \A e1, e2 \in 1..Executors:
        (e1 /= e2) => ~(
            /\ tasks[e1] /= NoTask
            /\ tasks[e1].kind = "Execution"
            /\ tasks[e2] = tasks[e1]
        )

AllDone == \A e \in 1..Executors: terminated[e]

Properties ==
    /\ Tx!Properties
    /\ [](AllDone => []AllDone)
    /\ [](AllDone => Tx!Committed(BlockSize))

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

================================================================================
