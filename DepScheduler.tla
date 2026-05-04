------------------------------ MODULE DepScheduler ------------------------------
\* An execution scheduler built on top of Dependency.tla's push validation design.
\*
\* Design goals:
\*   1. Prioritize low-index transactions, like all Block-STM variants.
\*   2. Use dependency information from push validation: don't schedule a
\*      transaction until its direct AND indirect dependencies are all executed.
\*   3. Respect incarnations: a dependency pins a specific writer incarnation;
\*      if the writer has advanced past that incarnation, the dep is stale and
\*      can be ignored (the writer's read/write sets may have changed).
\*
\* Scheduling model:
\*   - A fixed pool of executors each fetch the lowest-index schedulable
\*     transaction, execute it (TxBegin + TxExecute), and repeat.
\*   - "Schedulable" means: ReadyToExecute AND all transitive dependency writers
\*     have execStatus[w] = "Executed" (i.e., the writer has finished its
\*     current incarnation).  Stale deps (where the writer has advanced past
\*     the recorded incarnation) are skipped by TxBegin, but the scheduler's
\*     transitive check is a conservative heuristic for efficiency.
\*   - Between TxBegin and TxExecute, push validation (from another executor's
\*     TxExecute) may abort the transaction back to ReadyToExecute.  The
\*     executor detects this and simply drops the task to retry later.
\*
\* Indirect dependencies are checked transitively: if r depends on w, and w
\* depends on v, the scheduler won't schedule r until v AND w are both
\* Executed.  This prevents scheduling a transaction that can't make progress.
\*
\* The deps graph is guaranteed acyclic (DepsAcyclic in Dependency.tla) because
\* push validation only creates deps from lower-index writers to higher-index
\* readers, so the graph edges always go from smaller to larger indices.

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Key, NoVal, BlockSize, Executors

Dep == INSTANCE Dependency

ASSUME Executors # {}

VARIABLES
    \* All Dependency variables (shared mutable state)
    mem, rels, execStatus, incarnation, deps, txKeys,
    \* Scheduler-specific variables
    tasks,          \* [Executors -> Task \union {NoTask}]
                    \* The current transaction assigned to each executor.
    terminated      \* [Executors -> BOOLEAN]
                    \* Whether each executor has finished all work.

\* A task records the transaction assigned to an executor.
Task == [txn: Dep!TxIndex]
NoTask == CHOOSE t: t \notin Task

vars == << mem, rels, execStatus, incarnation, deps, txKeys, tasks, terminated >>

\* ============================================================================
\* Scheduling helpers
\* ============================================================================

\* Compute the set of all writers that txn transitively depends on through
\* the deps chain.  Since deps are acyclic (only smaller indices), the
\* recursion always terminates.
RECURSIVE TransitiveDeps(_)
TransitiveDeps(r) ==
    IF r \notin Dep!TxIndex THEN {}
    ELSE LET direct == { dep.w : dep \in deps[r] }
    IN direct \cup (UNION { TransitiveDeps(w) : w \in direct })

\* A transaction is schedulable when:
\*   1. It is ReadyToExecute (not already running or finished).
\*   2. All transitive dependency writers are Executed (finished their latest
\*      incarnation).  This includes both direct deps and indirect deps
\*      (deps of deps).  The scheduler conservatively waits for all transitive
\*      deps to finish, even though some may be stale (writer advanced past
\*      the recorded incarnation).  The precise incarnation check happens in
\*      TxBegin, so being slightly conservative here is safe.
\*
\* Stale deps (incarnation[dep.w] > dep.incn) could theoretically be skipped,
\* but the transitive check ensures we never schedule a transaction into a
\* state where its transitive deps are actively running or pending.  This
\* reduces unnecessary aborts and re-executions.
IsSchedulable(txn) ==
    /\ execStatus[txn] = "ReadyToExecute"
    /\ \A w \in TransitiveDeps(txn) : execStatus[w] = "Executed"

\* Find the best (lowest-index) schedulable transaction that is not already
\* assigned to any executor.  Returns NoTask if none is available.
BestNextTxn ==
    LET ready == { txn \in Dep!TxIndex :
        /\ IsSchedulable(txn)
        \* Exclude transactions already assigned to an executor.
        /\ \A e \in Executors : tasks[e] = NoTask \/ tasks[e].txn /= txn }
    IN IF ready = {} THEN NoTask
       ELSE CHOOSE txn \in ready : \A t \in ready : txn <= t

\* ============================================================================
\* State predicates
\* ============================================================================

TypeOK ==
    /\ Dep!TypeOK
    /\ tasks \in [Executors -> Task \union {NoTask}]
    /\ terminated \in [Executors -> BOOLEAN]

\* All executors have terminated (all work done).
AllTerminated == \A e \in Executors : terminated[e]

\* All transactions are Executed (the global done condition).
AllDone == \A txn \in Dep!TxIndex : execStatus[txn] = "Executed"

\* ============================================================================
\* Actions
\* ============================================================================

Init ==
    /\ Dep!Init
    /\ tasks = [e \in Executors |-> NoTask]
    /\ terminated = [e \in Executors |-> FALSE]

\* --- Executor lifecycle ---

\* An idle executor picks the best schedulable transaction and begins it.
\* TxBegin transitions ReadyToExecute -> Executing, registers reads in rels,
\* clears deps[txn] (after checking they're satisfied), and records the
\* incarnation in the rels entry.
Dispatch(e) ==
    /\ ~terminated[e]
    /\ tasks[e] = NoTask
    /\ LET txn == BestNextTxn IN
       txn /= NoTask
    /\ Dep!TxBegin(txn)
    /\ tasks' = [tasks EXCEPT ![e] = [txn |-> txn]]
    /\ UNCHANGED << terminated >>

\* An executor that has a task either:
\*   a) Completes the transaction (calls Dep!TxExecute) if it's still Executing,
\*      transitioning Executing -> Executed and running push validation.
\*   b) Drops the task if the transaction was push-invalidated by another
\*      executor's TxExecute (status is back to ReadyToExecute).
\*
\* In case (a), Dep!TxExecute may also push-invalidate other transactions that
\* are currently Executing or Executed, setting them back to ReadyToExecute
\* with incremented incarnation and updated deps.
ExecTask(e) ==
    /\ ~terminated[e]
    /\ tasks[e] /= NoTask
    /\ LET txn == tasks[e].txn IN
       IF execStatus[txn] = "Executing"
         THEN Dep!TxExecute(txn)
         ELSE \* Transaction was push-invalidated (back to ReadyToExecute)
              UNCHANGED << mem, rels, execStatus, incarnation, deps, txKeys >>
    /\ tasks' = [tasks EXCEPT ![e] = NoTask]
    /\ UNCHANGED << terminated >>

\* An executor that is idle and all work is done terminates itself.
CheckDone(e) ==
    /\ ~terminated[e]
    /\ tasks[e] = NoTask
    /\ AllDone
    /\ terminated' = [terminated EXCEPT ![e] = TRUE]
    /\ UNCHANGED << mem, rels, execStatus, incarnation, deps, txKeys, tasks >>

\* ============================================================================
\* Top-level next-state relation
\* ============================================================================

Next ==
    \/ AllTerminated /\ UNCHANGED vars
    \/ \E e \in Executors : CheckDone(e)
    \/ \E e \in Executors : Dispatch(e)
    \/ \E e \in Executors : ExecTask(e)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ============================================================================
\* Invariants
\* ============================================================================

\* No two executors can have the same transaction assigned.
NoConcurrentAssignment ==
    \A e1, e2 \in Executors :
        (e1 /= e2) => ~(tasks[e1] /= NoTask /\ tasks[e2] /= NoTask
                         /\ tasks[e1].txn = tasks[e2].txn)

\* An executor only has a task if that task's transaction is Executing
\* (meaning the executor called TxBegin and hasn't called TxExecute yet,
\* OR the executor is about to call TxExecute but hasn't yet).
\* If the transaction is push-invalidated back to ReadyToExecute, the
\* executor will drop it on its next ExecTask step.
ExecutorHasValidTask ==
    \A e \in Executors :
        tasks[e] /= NoTask => execStatus[tasks[e].txn] \in {"Executing"}

\* The same invariants from Dependency.tla still hold (inherited through Dep!TypeOK).
\* Additional scheduler invariants:
\*   - AllTerminated implies AllDone (executors only terminate when all done)
\*   - No transaction is stuck ReadyToExecute with empty deps when all executors idle
\*     (the scheduler will always pick it).

\* ============================================================================
\* Properties
\* ============================================================================

\* All transactions eventually complete.
EventuallyAllDone == <>[]AllDone

\* The scheduler makes progress: if there is a schedulable transaction and
\* an idle executor, something happens.
SchedulerProgress ==
    []( (\E e \in Executors : tasks[e] = NoTask /\ ~terminated[e])
        /\ \E txn \in Dep!TxIndex : IsSchedulable(txn)
        => <>(~(\E e \in Executors : tasks[e] = NoTask /\ ~terminated[e])
              \/ ~\E txn \in Dep!TxIndex : IsSchedulable(txn)))

\* The sequential consistency invariant from Dependency.tla.
FinalEqualsSequentialInv ==
    AllDone => \A txn \in Dep!TxIndex : Dep!ViewMem(txn + 1) = Dep!SeqStateAt[txn]

\* ============================================================================
\end