------------------------------ MODULE Dependency -------------------------------

EXTENDS Integers

CONSTANTS Key, NoVal, BlockSize

ASSUME BlockSize > 0

VARIABLES
    mem,        \* multi-version memory
    rels,       \* dependency relationships: key -> writer -> {[r: reader_tx, incn: incarnation]}
                \* Each entry records WHICH incarnation of a reader read from which writer.
                \* Multiple incarnations of the same transaction may coexist in rels under
                \* different writers (e.g., r5_1 under w1 and r5_2 under w3 for the same key).
                \* Read operations lazily ADD a new (r, incn) entry without removing old ones.
                \* Write operations handle displacement: they move ALL incarnation entries for
                \* affected readers and use the maximum displaced incarnation to decide aborts.
    execStatus, \* execution status of each transaction
    incarnation, \* incarnation number: monotonically increasing counter tracking
                 \* distinct "runs" of a transaction; a higher value means a newer
                 \* run, and different incarnations may read different versions of
                 \* the same key.  When a transaction is aborted its incarnation is
                 \* incremented and it transitions to ReadyToExecute for re-execution
                 \* at the new (higher) incarnation.  The CURRENT run is always the
                 \* biggest incarnation.
    deps,       \* scheduling dependency: deps[r] = set of writers that have
                \* push-invalidated txn r and whose current incarnation r must wait
                \* for before re-executing.  Specifically, txn r can only call TxBegin
                \* when execStatus[w] = "Executed" for every w in deps[r], ensuring
                \* that r reads from the LATEST writes of every writer that aborted it.
                \* deps[r] is cleared to {} when r calls TxBegin (which checks that
                \* all deps are already Executed at that point).
                \* If a writer w is itself re-aborted (set back to ReadyToExecute) after
                \* invalidating r, then r stays blocked until w finishes its new run.
    txKeys      \* txKeys[i] = subset of Key that transaction i reads and writes (may be empty).
                \* Chosen non-deterministically at Init and fixed for the whole execution,
                \* giving each transaction its own access pattern and producing diverse
                \* inter-transaction dependency graphs (some transactions share keys,
                \* others are independent, and some may touch no keys at all).

Storage == [k \in Key |-> 0]

INSTANCE Mem WITH Val <- 0..BlockSize

\* Transaction write function: txn increments exactly the keys in txKeys[txn].
\* Using a per-transaction key subset creates varied access patterns and diverse
\* inter-transaction dependency graphs (overlapping, non-overlapping, partial, or empty).
\* Value bound: Storage starts at 0; each key is incremented by at most one
\* transaction per sequential step, so values stay within Val = 0..BlockSize.
TxWrite(txn, reads) == [k \in txKeys[txn] |-> reads[k] + 1]

\* Apply transaction txn to a storage state.
ApplyTxAt(txn, st) == ApplyChanges(st, TxWrite(txn, st))

\* TxIndex extended with 0 to represent the initial version (writer 0 = storage).
WriterIndex == TxIndex \union {0}

\* Read-entry record: which reader, at which incarnation, read from a given writer.
\* rels[k][w] is a set of such records.  The same reader r may appear with different
\* incarnation values (under the same or different writers for the same key) because
\* successive re-executions may resolve FindMem to different writers.
REntry == [r : TxIndex, incn : Nat]

\* Type documentation (not used directly in TypeOK to avoid infinite-set issues with Nat).
Relationship == [Key -> [WriterIndex -> SUBSET REntry]]

ExecStatus == {"ReadyToExecute", "Executing", "Executed"}

vars == << mem, rels, execStatus, incarnation, deps, txKeys >>

TypeOK ==
    /\ TypeOKMem
    /\ \A k \in Key : \A w \in WriterIndex : \A e \in rels[k][w] :
        /\ e.r \in TxIndex
        /\ e.incn \in Nat
        /\ e.incn <= incarnation[e.r]   \* entries never exceed current incarnation
    /\ execStatus \in [TxIndex -> ExecStatus]
    /\ incarnation \in [TxIndex -> Nat]
    /\ deps \in [TxIndex -> SUBSET TxIndex]
    /\ txKeys \in [TxIndex -> SUBSET Key]

\* Specification

\* when a writer writes a key, readers that previously read from an older writer
\* for the same key are updated to point to the new writer.
\* "movers" are REntry records (r, incn) where r > w and the entry currently resides
\* under some writer < w.  ALL incarnation entries for such readers are moved together.
\*
\* Existing entries in relations[k][w] represent reads from w's PREVIOUS incarnation
\* (if w is re-executing).  We deliberately do NOT preserve them: they are dropped so
\* that InvalidatedReaders detects them as displaced and re-invalidates those readers.
\* On w's first execution relations[k][w] is empty, so the behaviour is identical.
RecordWrite(relations, w, keys) ==
    [ k \in Key |->
        IF k \notin keys
        THEN relations[k]
        ELSE
            LET prev_writers == { wi \in WriterIndex : wi < w }
                movers       == { e \in UNION { relations[k][wi] : wi \in prev_writers } :
                                      e.r > w }
            IN
            [ w2 \in WriterIndex |->
                IF w2 = w
                THEN movers
                ELSE relations[k][w2] \ movers
            ]
    ]

\* when a writer removes a key, e.g. a new incarnation doesn't write a key that was written before,
\* move readers that depended on this writer for the key to the previous writer that remains visible.
RecordRemove(relations, w, keys) ==
    [ k \in Key |->
        IF k \notin keys
        THEN relations[k]
        ELSE
            LET candidates == { wi \in WriterIndex :
                                 /\ wi < w
                                 /\ wi # 0
                                 /\ k \in DOMAIN mem[wi] }
                prevW == IF candidates = {}
                         THEN 0
                         ELSE CHOOSE wi \in candidates :
                                  \A wj \in candidates : wi >= wj
            IN
            [ w2 \in WriterIndex |->
                IF w2 = w
                THEN {}
                ELSE IF w2 = prevW
                     THEN relations[k][w2] \union relations[k][w]
                     ELSE relations[k][w2]
            ]
    ]

\* Compute the set of readers to abort after a write.
\*
\* A read entry e = [r, incn] is "displaced" when it was under some writer w in old_rels
\* but is no longer there in new_rels (RecordWrite moved it to the new writer).
\*
\* For each displaced reader r, find the MAXIMUM displaced incarnation max_n.  We abort r
\* only when:
\*   - incarnation[r] = max_n   — the displacement affects r's CURRENT run, and
\*   - execStatus[r] \in {"Executing", "Executed"} — r has registered its reads for that run.
\*
\* Both Executing and Executed readers have their reads registered in rels (via TxBegin) and
\* can therefore be aborted by a concurrent write.  A ReadyToExecute reader has not started
\* its current run yet and has no current-incarnation reads in rels; it is not aborted.
\*
\* Example: r5_incn1 resides under w1, r5_incn2 resides under w3.
\*   - w2 displaces only r5_incn1  → max_n=1.  If incarnation[r5]=2, no abort (r5 already
\*     re-executed past incarnation 1).
\*   - w4 displaces both r5_incn1 and r5_incn2 → max_n=2.  If incarnation[r5]=2 and
\*     execStatus[r5] ∈ {"Executing", "Executed"}, abort r5 (increment incarnation to 3,
\*     reschedule).
\*
\* If incarnation[r] > max_n: r has already re-executed to a newer incarnation; don't abort.
\* If execStatus[r] = "ReadyToExecute": r is already pending re-execution; don't abort again.
InvalidatedReaders(old_rels, new_rels) ==
    LET displaced == UNION { { e \in old_rels[k][w] : e \notin new_rels[k][w] }
                             : k \in Key, w \in WriterIndex }
    IN { r \in { e.r : e \in displaced } :
            \* disp_incns is non-empty: r was selected because it appears in displaced,
            \* so there is at least one entry with r.r = r.
            \* CHOOSE is the idiomatic TLA+ way to express "max of a non-empty finite set".
            LET disp_incns == { e.incn : e \in { d \in displaced : d.r = r } }
                max_n      == CHOOSE n \in disp_incns : \A m \in disp_incns : n >= m
            IN  /\ execStatus[r] \in {"Executing", "Executed"}
                /\ incarnation[r] = max_n }

\* Start executing transaction txn.  Transitions ReadyToExecute → Executing.
\*   - Checks and clears scheduling deps: txn may not start until every writer that
\*     previously push-aborted txn has finished its current incarnation (Executed).
\*   - Eagerly registers txn's reads in rels by adding [r: txn, incn: incarnation[txn]]
\*     under the nearest prior writer, but ONLY for keys in txKeys[txn].  This
\*     pre-registration is what enables push validation to abort an in-progress
\*     execution (Executing state): if a concurrent writer displaces one of these
\*     entries before TxExecute fires, InvalidatedReaders detects the displacement
\*     and sets txn back to ReadyToExecute.
TxBegin(txn) ==
    /\ execStatus[txn] = "ReadyToExecute"
    /\ \A w \in deps[txn] : execStatus[w] = "Executed"
    /\ LET entry == [r |-> txn, incn |-> incarnation[txn]]
           \* Only register reads for the keys this transaction actually accesses.
           \* Keys outside txKeys[txn] are not read, so no dependency entry is needed.
       IN rels' = [k \in Key |->
                     IF k \notin txKeys[txn]
                     THEN rels[k]
                     ELSE
                         LET w == FindMem(k, txn)
                         IN [ w2 \in WriterIndex |->
                                 IF w2 = w THEN rels[k][w2] \union {entry}
                                 ELSE rels[k][w2]
                            ]
                 ]
    /\ execStatus' = [execStatus EXCEPT ![txn] = "Executing"]
    /\ deps' = [deps EXCEPT ![txn] = {}]
    /\ UNCHANGED << mem, incarnation, txKeys >>

\* Commit the execution of txn.  Transitions Executing → Executed.
\* Reads were already registered in TxBegin (rels_reads == rels at this point).
\* Here we apply the chosen write-set and run push validation:
\*   1. Record writes — apply RecordWrite then RecordRemove to propagate the new write
\*                      to dependent readers (moves REntry records).
\*   2. Push validation — computes displaced entries; finds max incarnation per reader;
\*                        aborts Executing and Executed readers whose CURRENT incarnation
\*                        was displaced (incarnation[r] = max_n).  Aborted readers have
\*                        ALL their rels entries removed (rels_clean), gain txn in
\*                        deps[r], and are set back to ReadyToExecute with incarnation
\*                        incremented.  ReadyToExecute readers are untouched.
TxExecute(txn) ==
    /\ execStatus[txn] = "Executing"
    /\ LET
            \* Deterministic write-set: TxWrite applied to txn's read view.
            \* Only keys in txKeys[txn] are written; other keys are unaffected.
            cs         == TxWrite(txn, ViewMem(txn))
            \* Reads were pre-registered by TxBegin; current rels IS the pre-read snapshot.
            \* We keep the name rels_reads to make the three-step read→write→validate
            \* pipeline explicit and consistent with RecordWrite/RecordRemove signatures.
            rels_reads == rels
            \* Step 1a: record newly written keys
            rels_wrote == RecordWrite(rels_reads, txn, DOMAIN cs)
            \* Step 1b: remove keys not written in this incarnation
            rels_new   == RecordRemove(rels_wrote, txn, DOMAIN mem[txn] \ DOMAIN cs)
            \* Step 2: readers displaced by the write (uses max-incarnation rule).
            \* Both Executing and Executed readers are eligible for abort.
            inv        == InvalidatedReaders(rels_reads, rels_new)
            \* Remove ALL rels entries for aborted readers (ALL incarnations), since
            \* those entries are now stale: the reader will re-execute at a higher
            \* incarnation, and its new reads will create fresh entries in TxBegin.
            \* The scheduling obligation (re-execute only after deps are Executed)
            \* is captured in deps[r].
            rels_clean == [ k \in Key |->
                [ w \in WriterIndex |->
                    { e \in rels_new[k][w] : e.r \notin inv } ] ]
       IN
            /\ WriteMem(txn, cs)
            /\ rels' = rels_clean
            /\ execStatus' = [i \in TxIndex |->
                  IF i = txn   THEN "Executed"
                  ELSE IF i \in inv THEN "ReadyToExecute"
                  ELSE execStatus[i]]
            /\ incarnation' = [i \in TxIndex |->
                  IF i \in inv THEN incarnation[i] + 1
                  ELSE incarnation[i]]
            \* Aborted readers gain txn in their deps so they wait for txn's current
            \* incarnation to finish before re-executing at the higher incarnation.
            /\ deps' = [i \in TxIndex |->
                  IF i \in inv THEN deps[i] \union {txn}
                  ELSE deps[i]]
            /\ UNCHANGED txKeys

AllExecuted == \A txn \in TxIndex : execStatus[txn] = "Executed"

\* incarnation is strictly non-decreasing: each abort increments it, never rolls back.
IncarnationMonotone ==
    [][\A txn \in TxIndex : incarnation[txn] <= incarnation'[txn]]_vars

\* Liveness: eventually all transactions have completed their execution and the
\* system has stabilised.  Once AllExecuted is reached the only enabled step is
\* the stutter transition, so the state remains AllExecuted forever.
EventuallyAllExecuted == <>[]AllExecuted

\* Liveness: every Executing transaction eventually leaves that state — either it
\* finishes (Executing → Executed via TxExecute) or gets push-aborted by a concurrent
\* writer (Executing → ReadyToExecute via InvalidatedReaders in another TxExecute).
\* Together with EventuallyAllExecuted, this ensures no transaction is stuck forever in
\* a non-terminal state, i.e. the abortion logic is complete: every transaction in a
\* dirty/in-progress state will eventually be detected, aborted if needed, and
\* re-executed with fresh reads until it stabilises at Executed.
AbortCompleteness ==
    \A r \in TxIndex :
        (execStatus[r] = "Executing") ~> (execStatus[r] /= "Executing")

Init ==
    /\ InitMem
    /\ txKeys      \in [TxIndex -> SUBSET Key]
    /\ rels        = [ k \in Key |-> [w \in WriterIndex |-> {}] ]
    /\ execStatus  = [i \in TxIndex |-> "ReadyToExecute"]
    /\ incarnation = [i \in TxIndex |-> 0]
    /\ deps        = [i \in TxIndex |-> {}]

Next ==
    \/ AllExecuted /\ UNCHANGED vars
    \/ \E txn \in TxIndex : TxBegin(txn)
    \/ \E txn \in TxIndex : TxExecute(txn)

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* Properties

\* reader is always after the writer for all relationships, i.e. a reader always reads the previous version of a key.
ReadPreviousVersion ==
    \A k \in Key: \A w \in WriterIndex: \A e \in rels[k][w]:
        w < e.r

(* A reader always reads the latest value before it,
 * aka. there is no writes between a reader and a writer,
 * for all relationships, for all txn in (w, r), mem[txn] does not contain the key.
 *)
NoWriteInBetween ==
    \A k \in Key: \A w \in WriterIndex: \A e \in rels[k][w]:
        \A txn \in (w + 1)..(e.r - 1):
            k \notin DOMAIN mem[txn]

\* the writer performed an operation (write or delete) on the key for all relationships, i.e. the relationship is not spurious.
ConsistentReads ==
    \A k \in Key: \A w \in TxIndex:
        rels[k][w] /= {} => k \in DOMAIN mem[w]

\* all the readers that read a writer are <= the next writer for the same key, i.e. the relationships do not overlap.
RelationshipsDontOverlap ==
    \A k \in Key: \A w1, w2 \in WriterIndex: \A e1 \in rels[k][w1]: \A e2 \in rels[k][w2]:
        w1 < w2 => e1.r <= w2

\* each (reader, incarnation) pair reads from at most one writer per key.
\* Different incarnations of the same reader may read from different writers (lazy cleanup),
\* so uniqueness is per (reader, incarnation) pair — not per reader alone.
UniqueReaderIncarnations ==
    \A k \in Key: \A w1, w2 \in WriterIndex: \A e \in rels[k][w1]:
        e \in rels[k][w2] => w1 = w2

\* deps[r] only contains writers with a strictly smaller transaction index than r.
\* Because RecordWrite only moves REntry records whose e.r > writer, every writer
\* that can push-invalidate r has index < r.  This guarantees the deps graph is
\* acyclic, so the system can never deadlock waiting for scheduling dependencies.
DepsAcyclic ==
    \A r \in TxIndex : \A w \in deps[r] : w < r

\* deps[r] is non-empty only while r is still pending re-execution (ReadyToExecute).
\* TxBegin clears deps[r] when r starts executing (transitions to Executing), after
\* verifying that all scheduling dependencies are satisfied.  While r is Executing
\* or Executed, deps[r] = {}.
DepsOnlyForPending ==
    \A r \in TxIndex : deps[r] /= {} => execStatus[r] = "ReadyToExecute"

THEOREM NoWriteInBetween /\ ConsistentReads => RelationshipsDontOverlap

\* Sequential execution state at step i: apply ApplyTxAt iteratively starting from
\* Storage, without any reference to mem.  This gives the ground-truth result of
\* running transactions 1..i in program order, each reading from the output of the
\* previous transaction.  SeqStateAt[0] = Storage (base case, no transactions applied).
\* Each transaction only reads/writes its own key subset txKeys[txn], so transactions
\* with non-overlapping key sets are independent and those with overlap must be
\* re-executed when a prior dependent transaction's output changes.
SeqStateAt[i \in 0..BlockSize] ==
    IF i = 0 THEN Storage
    ELSE ApplyTxAt(i, SeqStateAt[i - 1])

\* When all transactions have been executed, the view seen after every transaction txn
\* must equal the sequential state produced by transactions 1..txn.  This is the
\* TLC-checkable form of FinalEqualsSequential below.  It checks every prefix, not
\* just the final result, so it catches any intermediate inconsistency.
FinalEqualsSequentialInv ==
    AllExecuted => \A txn \in TxIndex : ViewMem(txn + 1) = SeqStateAt[txn]

\* The final execution result of parallel multi-version execution equals the result
\* of applying each transaction's write set in sequential program order.
THEOREM FinalEqualsSequential ==
    ViewMem(BlockSize + 1) = SeqStateAt[BlockSize]

================================================================================
