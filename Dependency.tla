------------------------------ MODULE Dependency -------------------------------

EXTENDS Integers

CONSTANTS Key, Val, NoVal, BlockSize

ASSUME Val /= {}

VARIABLES
    mem,        \* multi-version memory
    rels,       \* dependency relationships: key -> writer -> {readers}
    execStatus, \* execution status of each transaction
    incarnation \* incarnation number of each transaction

Storage == [k \in Key |-> CHOOSE v \in Val : TRUE]

INSTANCE Mem

\* TxIndex extended with 0 to represent the initial version (writer 0 = storage).
WriterIndex == TxIndex \union {0}

\* Records which readers read a given key from a given writer.
\* key -> writer_tx -> { reader_tx }
\* writer_tx is 0 for the initial version.
Relationship == [Key -> [WriterIndex -> SUBSET TxIndex]]

ExecStatus == {"ReadyToExecute", "Executed"}

vars == << mem, rels, execStatus, incarnation >>

TypeOK ==
    /\ TypeOKMem
    /\ rels \in Relationship
    /\ execStatus \in [TxIndex -> ExecStatus]
    /\ incarnation \in [TxIndex -> Nat]

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

\* Compute the set of readers whose dependency was removed:
\* any reader that appears in some writer's set in old_rels but not in the same
\* set in new_rels.  These readers must re-execute because a write has changed
\* the version they depend on (push validation).
InvalidatedReaders(old_rels, new_rels) ==
    { r \in TxIndex :
        \E k \in Key : \E w \in WriterIndex :
            r \in old_rels[k][w] /\ r \notin new_rels[k][w] }

\* Execute transaction txn atomically:
\*   1. Record reads  – update rels so txn points to the nearest prior writer for
\*                      every key, removing any stale entries from previous reads.
\*   2. Record writes – apply RecordWrite then RecordRemove to propagate the new
\*                      write to dependent readers.
\*   3. Push validation – any reader whose dependency changed is immediately
\*                        re-scheduled (execStatus -> ReadyToExecute) and its
\*                        incarnation is incremented; txn itself moves to Executed.
TxExecute(txn) ==
    /\ execStatus[txn] = "ReadyToExecute"
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
        IN
            /\ WriteMem(txn, cs)
            /\ rels' = rels_new
            /\ execStatus' = [i \in TxIndex |->
                  IF i = txn   THEN "Executed"
                  ELSE IF i \in inv THEN "ReadyToExecute"
                  ELSE execStatus[i]]
            /\ incarnation' = [i \in TxIndex |->
                  IF i \in inv THEN incarnation[i] + 1
                  ELSE incarnation[i]]

AllExecuted == \A txn \in TxIndex : execStatus[txn] = "Executed"

Init ==
    /\ InitMem
    /\ rels        = [ k \in Key |-> [w \in WriterIndex |-> {}] ]
    /\ execStatus  = [i \in TxIndex |-> "ReadyToExecute"]
    /\ incarnation = [i \in TxIndex |-> 0]

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

THEOREM NoWriteInBetween /\ ConsistentReads => RelationshipsDontOverlap

================================================================================
