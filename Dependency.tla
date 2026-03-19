------------------------------ MODULE Dependency -------------------------------

EXTENDS Integers

CONSTANTS Key, Val, NoVal, BlockSize

ASSUME Val /= {}

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
    deps        \* scheduling dependency: deps[r] = set of writers that have
                \* push-invalidated txn r and whose current incarnation r must wait
                \* for before re-executing.  Specifically, txn r can re-execute only
                \* when execStatus[w] = "Executed" for every w in deps[r], ensuring
                \* that r reads from the LATEST writes of every writer that aborted it.
                \* deps[r] is cleared to {} when r re-executes (its precondition
                \* guarantees all writers are already Executed at that point).
                \* If a writer w is itself re-aborted (set back to ReadyToExecute) after
                \* invalidating r, then r stays blocked until w finishes its new run.

Storage == [k \in Key |-> CHOOSE v \in Val : TRUE]

INSTANCE Mem

\* TxIndex extended with 0 to represent the initial version (writer 0 = storage).
WriterIndex == TxIndex \union {0}

\* Read-entry record: which reader, at which incarnation, read from a given writer.
\* rels[k][w] is a set of such records.  The same reader r may appear with different
\* incarnation values (under the same or different writers for the same key) because
\* successive re-executions may resolve FindMem to different writers.
REntry == [r : TxIndex, incn : Nat]

\* Type documentation (not used directly in TypeOK to avoid infinite-set issues with Nat).
Relationship == [Key -> [WriterIndex -> SUBSET REntry]]

ExecStatus == {"ReadyToExecute", "Executed"}

vars == << mem, rels, execStatus, incarnation, deps >>

TypeOK ==
    /\ TypeOKMem
    /\ \A k \in Key : \A w \in WriterIndex : \A e \in rels[k][w] :
        /\ e.r \in TxIndex
        /\ e.incn \in Nat
        /\ e.incn <= incarnation[e.r]   \* entries never exceed current incarnation
    /\ execStatus \in [TxIndex -> ExecStatus]
    /\ incarnation \in [TxIndex -> Nat]
    /\ deps \in [TxIndex -> SUBSET TxIndex]

\* Specification

\* when a writer writes a key, readers that previously read from an older writer
\* for the same key are updated to point to the new writer.
\* "movers" are REntry records (r, incn) where r > w and the entry currently resides
\* under some writer < w.  ALL incarnation entries for such readers are moved together.
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
                THEN relations[k][w2] \union movers
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
\*   - execStatus[r] = "Executed" — r has actually finished that run.
\*
\* Example: r5_incn1 resides under w1, r5_incn2 resides under w3.
\*   - w2 displaces only r5_incn1  → max_n=1.  If incarnation[r5]=2, no abort (r5 already
\*     re-executed past incarnation 1).
\*   - w4 displaces both r5_incn1 and r5_incn2 → max_n=2.  If incarnation[r5]=2 and
\*     execStatus[r5]="Executed", abort r5 (increment incarnation to 3, reschedule).
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
            IN  /\ execStatus[r] = "Executed"
                /\ incarnation[r] = max_n }

\* Execute transaction txn atomically:
\*   1. Record reads  – lazily ADD a new [r: txn, incn: incarnation[txn]] entry for every
\*                      key to the correct writer's set (FindMem).  Old entries from previous
\*                      incarnations of txn are left in place: different incarnations of txn
\*                      may read from different writers, so their entries coexist in rels.
\*                      Write operations handle displacement and cleanup lazily.
\*   2. Record writes – apply RecordWrite then RecordRemove to propagate the new write
\*                      to dependent readers (moves REntry records, not plain reader ids).
\*   3. Push validation – compute displaced entries, find max incarnation per reader,
\*                        and abort only readers whose CURRENT incarnation was displaced
\*                        (incarnation[r] = max_n) and who have finished that run (Executed).
\*                        Aborted readers have ALL their rels entries removed (rels_clean),
\*                        gain txn in deps[r], and are set back to ReadyToExecute with
\*                        incarnation incremented.  ReadyToExecute readers are untouched.
\* Precondition: all writers in deps[txn] must be Executed, guaranteeing that txn
\* reads from the latest writes of every writer that previously aborted it.
TxExecute(txn) ==
    /\ execStatus[txn] = "ReadyToExecute"
    /\ \A w \in deps[txn] : execStatus[w] = "Executed"
    /\ \E cs \in Overlay :
        LET
            \* Step 1: lazily record reads – add new (txn, current incarnation) entry
            \* to the appropriate writer's set; do NOT remove old incarnation entries.
            rels_reads == [k \in Key |->
                LET w     == FindMem(k, txn)
                    entry == [r |-> txn, incn |-> incarnation[txn]]
                IN [ w2 \in WriterIndex |->
                    IF w2 = w THEN rels[k][w2] \union {entry}
                    ELSE rels[k][w2]
                ]
            ]
            \* Step 2a: record newly written keys
            rels_wrote == RecordWrite(rels_reads, txn, DOMAIN cs)
            \* Step 2b: remove keys not written in this incarnation
            rels_new   == RecordRemove(rels_wrote, txn, DOMAIN mem[txn] \ DOMAIN cs)
            \* Step 3: readers displaced by the write (uses max-incarnation rule)
            inv        == InvalidatedReaders(rels_reads, rels_new)
            \* Remove ALL rels entries for aborted readers (ALL incarnations), since
            \* those entries are now stale: the reader will re-execute at a higher
            \* incarnation, and its new reads will create fresh entries.  This full
            \* cleanup is in contrast to the lazy ADD in Step 1: laziness applies
            \* during normal execution, but on abort we clear the slate so old
            \* incarnation entries don't interfere with future displacement checks.
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
            \* txn clears its own deps on re-execution (precondition guarantees
            \* they were all Executed); invalidated readers gain txn in their deps.
            /\ deps' = [i \in TxIndex |->
                  IF i = txn  THEN {}
                  ELSE IF i \in inv THEN deps[i] \union {txn}
                  ELSE deps[i]]

AllExecuted == \A txn \in TxIndex : execStatus[txn] = "Executed"

\* incarnation is strictly non-decreasing: each abort increments it, never rolls back.
IncarnationMonotone ==
    [][\A txn \in TxIndex : incarnation[txn] <= incarnation'[txn]]_vars

\* Liveness: eventually all transactions have completed their execution and the
\* system has stabilised.  Once AllExecuted is reached the only enabled step is
\* the stutter transition, so the state remains AllExecuted forever.
EventuallyAllExecuted == <>[]AllExecuted

Init ==
    /\ InitMem
    /\ rels        = [ k \in Key |-> [w \in WriterIndex |-> {}] ]
    /\ execStatus  = [i \in TxIndex |-> "ReadyToExecute"]
    /\ incarnation = [i \in TxIndex |-> 0]
    /\ deps        = [i \in TxIndex |-> {}]

Next ==
    \/ AllExecuted /\ UNCHANGED vars
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

\* deps[r] is non-empty only while r is still pending re-execution.
\* Once r re-executes (becomes Executed) its deps are cleared to {}.
DepsOnlyForPending ==
    \A r \in TxIndex : deps[r] /= {} => execStatus[r] = "ReadyToExecute"

THEOREM NoWriteInBetween /\ ConsistentReads => RelationshipsDontOverlap

================================================================================
