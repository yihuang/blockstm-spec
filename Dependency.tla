------------------------------ MODULE Dependency -------------------------------

EXTENDS Integers

CONSTANTS Key, Val, NoVal, BlockSize

ASSUME Val /= {}

VARIABLES
    mem,        \* multi-version memory
    rels,       \* dependency relationships: key -> writer -> {readers}
                \* ONLY contains entries for currently-Executed transactions whose
                \* reads are still valid.  Stale entries are removed immediately
                \* when a reader is push-invalidated, so invariants hold at all times.
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

\* Records which readers read a given key from a given writer.
\* key -> writer_tx -> { reader_tx }
\* writer_tx is 0 for the initial version.
Relationship == [Key -> [WriterIndex -> SUBSET TxIndex]]

ExecStatus == {"ReadyToExecute", "Executed"}

vars == << mem, rels, execStatus, incarnation, deps >>

TypeOK ==
    /\ TypeOKMem
    /\ rels \in Relationship
    /\ execStatus \in [TxIndex -> ExecStatus]
    /\ incarnation \in [TxIndex -> Nat]
    /\ deps \in [TxIndex -> SUBSET TxIndex]

\* Specification

\* when a writer writes a key, readers that previously read from an older writer
\* for the same key are updated to point to the new writer.
RecordWrite(relations, w, keys) ==
    [ k \in Key |->
        IF k \notin keys
        THEN relations[k]
        ELSE
            LET movers == { r \in TxIndex :
                    /\ r > w
                    /\ \E w_cur \in WriterIndex :
                        /\ w_cur < w
                        /\ r \in relations[k][w_cur] }
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

\* Compute the set of readers whose dependency pointer moved to a different writer
\* AND whose rels entry corresponds to the CURRENT (biggest) incarnation, i.e.
\* execStatus[r] = "Executed".
\*
\* A writer must only abort transactions that have COMPLETED execution at their
\* current incarnation.  If a reader is already ReadyToExecute — either awaiting
\* its first run or already re-scheduled to a higher incarnation by a prior write —
\* its rels entry is speculative/stale and must not trigger another abort.  This
\* ensures the writer aborts exactly the biggest incarnation and never re-aborts
\* an ongoing (higher-incarnation) re-execution.
InvalidatedReaders(old_rels, new_rels) ==
    { r \in TxIndex :
        /\ execStatus[r] = "Executed"
        /\ \E k \in Key : \E w \in WriterIndex :
            r \in old_rels[k][w] /\ r \notin new_rels[k][w] }

\* Execute transaction txn atomically:
\*   1. Record reads  – update rels so txn points to the nearest prior writer for
\*                      every key, removing any stale entries from previous incarnations.
\*                      Different incarnations of the same txn may read different
\*                      versions of the same key.
\*   2. Record writes – apply RecordWrite then RecordRemove to propagate the new
\*                      write to dependent readers.
\*   3. Push validation – only Executed readers whose dependency changed are
\*                        push-invalidated: their stale rels entries are REMOVED
\*                        entirely (rels stays clean, invariants intact), their
\*                        scheduling dependency deps[r] gains txn (so r waits for
\*                        txn's current incarnation before re-executing), execStatus
\*                        is set back to ReadyToExecute, and incarnation incremented.
\*                        ReadyToExecute readers are left untouched: they have
\*                        already been re-scheduled to a bigger incarnation and must
\*                        not be aborted again.
\* Precondition: all writers in deps[txn] must be Executed, guaranteeing that txn
\* reads from the latest writes of every writer that previously aborted it.
TxExecute(txn) ==
    /\ execStatus[txn] = "ReadyToExecute"
    /\ \A w \in deps[txn] : execStatus[w] = "Executed"
    /\ \E cs \in Overlay :
        LET
            \* Step 1: record reads for all keys
            rels_reads == [k \in Key |->
                LET w    == FindMem(k, txn)
                    prev == { w2 \in WriterIndex : txn \in rels[k][w2] }
                IN [ w2 \in WriterIndex |->
                    IF w2 = w      THEN rels[k][w2] \union {txn}
                    ELSE IF w2 \in prev THEN rels[k][w2] \ {txn}
                    ELSE rels[k][w2]
                ]
            ]
            \* Step 2a: record newly written keys
            rels_wrote == RecordWrite(rels_reads, txn, DOMAIN cs)
            \* Step 2b: remove keys not written in this incarnation
            rels_new   == RecordRemove(rels_wrote, txn, DOMAIN mem[txn] \ DOMAIN cs)
            \* Step 3: readers displaced by the write
            inv        == InvalidatedReaders(rels_reads, rels_new)
            \* Remove ALL stale rels entries for invalidated readers so that rels
            \* only ever contains entries for currently-valid (Executed) reads.
            \* The scheduling obligation is moved to deps instead.
            rels_clean == [ k \in Key |->
                [ w \in WriterIndex |->
                    rels_new[k][w] \ inv ] ]
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
    \A k \in Key: \A w \in WriterIndex: \A r \in rels[k][w]:
        w < r

(* A reader always reads the latest value before it,
 * aka. there is no writes between a reader and a writer,
 * for all relationships, for all txn in (w, r), mem[txn] does not contain the key.
 *)
NoWriteInBetween ==
    \A k \in Key: \A w \in WriterIndex: \A r \in rels[k][w]:
        \A txn \in (w + 1)..(r - 1):
            k \notin DOMAIN mem[txn]

\* the writer performed an operation (write or delete) on the key for all relationships, i.e. the relationship is not spurious.
ConsistentReads ==
    \A k \in Key: \A w \in TxIndex:
        rels[k][w] /= {} => k \in DOMAIN mem[w]

\* all the readers that read a writer are <= the next writer for the same key, i.e. the relationships do not overlap.
RelationshipsDontOverlap ==
    \A k \in Key: \A w1, w2 \in WriterIndex: \A r1 \in rels[k][w1]: \A r2 \in rels[k][w2]:
        w1 < w2 => r1 <= w2

\* each reader reads from at most one writer per key, i.e. readers are unique under the same key.
UniqueReaders ==
    \A k \in Key: \A r \in TxIndex: \A w1, w2 \in WriterIndex:
        r \in rels[k][w1] /\ r \in rels[k][w2] => w1 = w2

\* deps[r] only contains writers with a strictly smaller transaction index than r.
\* Because RecordWrite only moves readers with index > writer, every writer that can
\* push-invalidate r has index < r.  This guarantees the deps graph is acyclic, so
\* the system can never deadlock waiting for scheduling dependencies.
DepsAcyclic ==
    \A r \in TxIndex : \A w \in deps[r] : w < r

\* deps[r] is non-empty only while r is still pending re-execution.
\* Once r re-executes (becomes Executed) its deps are cleared to {}.
DepsOnlyForPending ==
    \A r \in TxIndex : deps[r] /= {} => execStatus[r] = "ReadyToExecute"

THEOREM NoWriteInBetween /\ ConsistentReads => RelationshipsDontOverlap

================================================================================
