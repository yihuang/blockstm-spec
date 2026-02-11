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
    execution_idx, \* the next transaction to execute
    validation_idx, \* the next transaction to validate
    tasks \* the current task of each executor

txVars == << mem, execStatus, incarnation, readSet >>
vars == << txVars, execution_idx, validation_idx, tasks >>

Task == [
    txn: Tx!TxIndex ,
    kind: {"Execution", "Validation"}
]
\* NoTask == CHOOSE t: t \notin Task

TypeOK ==
    /\ Tx!TypeOK
    /\ execution_idx \in 1..(BlockSize + 1)
    /\ validation_idx \in 1..(BlockSize + 1)
    /\ tasks \in [1..Executors -> Task \union {NoTask}]

Init ==
    /\ Tx!Init
    /\ execution_idx = 1
    /\ validation_idx = 1
    /\ tasks = [e \in 1..Executors |-> NoTask]

PreferValidation == validation_idx < execution_idx

NextTaskExecution(e) ==
    /\ ~PreferValidation
    /\ execution_idx < BlockSize + 1
    /\ execution_idx' = execution_idx + 1
    /\ tasks' = [tasks EXCEPT ![e] = [txn |-> execution_idx, kind |-> "Execution"]]
    /\ UNCHANGED << validation_idx, txVars >>

NextTaskValidation(e) ==
    /\ PreferValidation
    /\ validation_idx < BlockSize + 1
    /\ validation_idx' = validation_idx + 1
    /\ tasks' = [tasks EXCEPT ![e] = [txn |-> validation_idx, kind |-> "Validation"]]
    /\ UNCHANGED << execution_idx, txVars >>

FetchTask(e) ==
    /\ tasks[e] = NoTask
    /\ NextTaskExecution(e) \/ NextTaskValidation(e)

ResetValidationIdx(txn) ==
    IF txn < validation_idx THEN
        validation_idx' = txn
    ELSE UNCHANGED validation_idx

ExecuteTx(e) ==
    /\ tasks[e].kind = "Execution"
    /\ Tx!TxExecute(tasks[e].txn)
    /\ tasks' = [tasks EXCEPT ![e] = [@ EXCEPT !.kind = "Validation"]]
    /\ ResetValidationIdx(tasks[e].txn + 1)
    /\ UNCHANGED << execution_idx >>

ValidateTx(e) ==
    /\ tasks[e].kind = "Validation"
    /\
        \/ Tx!TxValidate(tasks[e].txn)
        \/ UNCHANGED txVars \* skip if tx is not ready to validate
    /\ tasks' = [tasks EXCEPT ![e] = NoTask]
    /\ UNCHANGED << execution_idx, validation_idx >>

ExecTask(e) ==
    /\ tasks[e] /= NoTask
    /\ ExecuteTx(e) \/ ValidateTx(e)

Executor(e) ==
    FetchTask(e) \/ ExecTask(e) \/ UNCHANGED vars

Next ==
    \E e \in 1..Executors:
        Executor(e)

Liveness == Tx!Liveness

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

================================================================================
