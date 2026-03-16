---- MODULE Dependency ----
EXTENDS Integers

CONSTANTS Key, NoVal, Absent, BlockSize

VARIABLE mem

Storage == [k \in Key |-> 0]

INSTANCE Mem WITH
    Val <- 0..1

VARIABLE rels \* relationships between read/write transactions

\* Records a reader read a key which is wrote by a writer.
\* 0 means the initial version, Absent means the reader don't read the key.
\* (reader_tx, key) -> writer_tx
Relationship == [TxIndex \X Key -> TxIndex \cup {0, Absent}]

TypeOK ==
    /\ TypeOKMem
    /\ rels \in Relationship

\* Specification

\* when reader reads a key from multi-version Mem module
RecordRead(r, k, w) == rels' = [rels EXCEPT ![<<r, k>>] = w]

\* when writer writes a key, the relationships that cross the writer should be updated.
RecordWrite(w, key) ==
    rels' = [ <<r, k>> \in TxIndex \X Key |->
        LET w_cur == rels[<<r, k>>] IN
        IF /\ w_cur /= Absent
           /\ k = key
           /\ r > w
           /\ w_cur < w
        THEN w
        ELSE w_cur
    ]

\* when writer remove a key, e.g. a new incarnation don't write a key that's written before,
\* remove the relationships that reads the writer for the key.
RecordRemove(w, key) ==
    rels' = [ <<r, k>> \in TxIndex \X Key |->
        LET w_cur == rels[<<r, k>>] IN
        IF k = key /\ w_cur = w
        THEN Absent
        ELSE w_cur
    ]

Write(w, cs) ==
    /\ WriteMem(w, cs)
    /\ IF cs = <<>> /\ mem[w] = <<>> THEN
        UNCHANGED rels
      ELSE
        /\ \A k \in DOMAIN cs: RecordWrite(w, k)
        /\ \A k \in DOMAIN mem[w] \ DOMAIN cs: RecordRemove(w, k)

Read(r, k) ==
    LET w == FindMem(k, r) IN
    /\ RecordRead(r, k, w)
    /\ UNCHANGED mem

Init ==
    /\ InitMem
    /\ rels = [<<r, k>> \in TxIndex \X Key |-> Absent]

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
    \A r \in TxIndex: \A k \in Key:
        LET w == rels[<<r, k>>] IN
            w = Absent \/ w < r

(* A reader always reads the latest value before it,
 * aka. there is no writes between a reader and a writer,
 * for all relationships, for all txn in (w, r), mem[txn] does not contain the key.
 *)
NoWriteInBetween ==
    \A r \in TxIndex: \A k \in Key:
        LET w == rels[<<r, k>>] IN
            \/ w = Absent
            \/ \A txn \in (w + 1)..(r - 1):
                  k \notin DOMAIN mem[txn]

\* the value do exists for all relationships, i.e. the relationship is not spurious.
ConsistentReads ==
    \A r \in TxIndex: \A k \in Key:
        LET w == rels[<<r, k>>] IN
            \/ w = Absent
            \/ w = 0
            \/ k \in DOMAIN mem[w]

\* all the readers that reads a writer are `<=` the next writer for the same key, i.e. the relationships do not cross each other.
RelationshipsDontOverlap ==
    \A r1, r2 \in TxIndex: \A k \in Key:
        LET w1 == rels[<<r1, k>>]
            w2 == rels[<<r2, k>>] IN
            \/ w1 = Absent
            \/ w2 = Absent
            \/ w1 < w2 => r1 <= w2

THEOREM NoWriteInBetween /\ ConsistentReads => RelationshipsDontOverlap

====
