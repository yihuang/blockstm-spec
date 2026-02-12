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
    tasks, \* the current task of each executor
    terminated, \* whether the executor is terminated
    active_tasks \* the number of currently active tasks

txVars == << mem, execStatus, incarnation, readSet >>
vars == << txVars, execution_idx, validation_idx, tasks, terminated, active_tasks >>

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
    /\ terminated \in [1..Executors -> BOOLEAN]
    /\ active_tasks \in 0..Executors

Init ==
    /\ Tx!Init
    /\ execution_idx = 1
    /\ validation_idx = 1
    /\ tasks = [e \in 1..Executors |-> NoTask]
    /\ terminated = [e \in 1..Executors |-> FALSE]
    /\ active_tasks = 0

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
    /\ UNCHANGED << terminated, txVars >>

ResetValidationIdx(txn) ==
    IF txn < validation_idx THEN
        validation_idx' = txn
    ELSE UNCHANGED validation_idx

ExecuteTx(e) ==
    /\ tasks[e].kind = "Execution"
    /\ Tx!TxExecute(tasks[e].txn)
    /\ IF tasks[e].txn < validation_idx THEN
         /\ tasks' = [tasks EXCEPT ![e] = [@ EXCEPT !.kind = "Validation"]]
         /\ ResetValidationIdx(tasks[e].txn + 1)
       ELSE
         /\ tasks' = [tasks EXCEPT ![e] = NoTask]
         /\ active_tasks' = active_tasks - 1
    /\ UNCHANGED << execution_idx, active_tasks >>

ValidateTx(e) ==
    /\ tasks[e].kind = "Validation"
    /\ LET txn == tasks[e].txn IN
        \/ /\ Tx!TxValidateAbort(txn)
          /\ tasks' = [tasks EXCEPT ![e] = [@ EXCEPT !.kind = "Execution"]]
          /\ UNCHANGED active_tasks
        \/ /\ Tx!TxValidateOK(txn)
          /\ tasks' = [tasks EXCEPT ![e] = NoTask]
          /\ active_tasks' = active_tasks - 1
        \/ /\ UNCHANGED << txVars, tasks >> \* skip if tx is not ready to validate
          /\ tasks' = [tasks EXCEPT ![e] = NoTask]
          /\ active_tasks' = active_tasks - 1
    /\ UNCHANGED << execution_idx, validation_idx >>

ExecTask(e) ==
    /\ tasks[e] /= NoTask
    /\ ExecuteTx(e) \/ ValidateTx(e)
    /\ UNCHANGED << terminated >>

CheckDone(e) ==
    /\ ~terminated[e]
    /\ validation_idx = BlockSize + 1
    /\ execution_idx = BlockSize + 1
    /\ active_tasks = 0
    /\ terminated' = [terminated EXCEPT ![e] = TRUE]
    /\ UNCHANGED << execution_idx, validation_idx, tasks, active_tasks, txVars >>

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

\* when executors are done, transactions must reach consistent final state
Consistency == [](AllDone => Tx!AllDone)

Liveness == <>[]AllDone

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

================================================================================
