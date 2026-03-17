------------------------------ MODULE Dependency -------------------------------

EXTENDS Integers

CONSTANTS Key, NoVal, BlockSize

VARIABLE mem

Storage == [k \in Key |-> 0]

INSTANCE Mem WITH
    Val <- 0..1

VARIABLE rels \* relationships between read/write transactions

\* TxIndex extended with 0 to represent the initial version (writer 0 = storage).
WriterIndex == TxIndex \union {0}

\* Records which readers read a given key from a given writer.
\* key -> writer_tx -> { reader_tx }
\* writer_tx is 0 for the initial version.
Relationship == [Key -> [WriterIndex -> SUBSET TxIndex]]

TypeOK ==
    /\ TypeOKMem
    /\ rels \in Relationship

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
\* remove the relationships that read the writer for the key.
RecordRemove(relations, w, keys) ==
    [ k \in Key |->
        IF k \notin keys
        THEN relations[k]
        ELSE
            [ w2 \in WriterIndex |->
                IF w2 = w
                THEN {}
                ELSE relations[k][w2]
            ]
    ]

Write(w, cs) ==
    /\ WriteMem(w, cs)
    /\ LET wrote == RecordWrite(rels, w, DOMAIN cs)
          removed == RecordRemove(wrote, w, DOMAIN mem[w] \ DOMAIN cs)
      IN
          rels' = removed

Read(r, k) ==
    LET w == FindMem(k, r)
        prev == { w2 \in WriterIndex : r \in rels[k][w2] }
    IN
        /\ rels' = [ rels EXCEPT
                ![k] = [ w2 \in WriterIndex |->
                    IF w2 = w THEN rels[k][w2] \union {r}
                    ELSE IF w2 \in prev THEN rels[k][w2] \ {r}
                    ELSE rels[k][w2]
                ]
            ]
        /\ UNCHANGED mem

Init ==
    /\ InitMem
    /\ rels = [ k \in Key |-> [w \in WriterIndex |-> {}] ]

Next ==
    \/ \E w \in TxIndex:
        \E cs \in Overlay:
            Write(w, cs)

    \/ \E r \in TxIndex:
        \E k \in Key:
            Read(r, k)

Spec ==
    Init /\ [][Next]_<< mem, rels >>

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
