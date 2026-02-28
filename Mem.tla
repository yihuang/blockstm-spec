---------------------------------- MODULE Mem ----------------------------------
EXTENDS Sequences, Integers

CONSTANTS Key, Val, NoVal, BlockSize

INSTANCE Store

(*
 * Mem is a naive implementation of multi-version memory,
 * where mem[i] is the overlay of changes for transaction i.
 *)

Max(s) == CHOOSE i \in s: \A j \in s: j <= i

TxIndex == 1..BlockSize

EmptyMem ==
    [i \in TxIndex |-> <<>>]

TypeOKMem(mem) ==
    mem \in [TxIndex -> Overlay]

(*
 * Find the version of key as seen by transaction txn,
 * i.e. the largest index i < txn such that mem[i] contains the key,
 * returns 0 if not found.
 *)
FindMem(mem, key, txn) ==
    LET cs == {i \in 1..(txn - 1): key \in DOMAIN mem[i]} IN
        IF cs = {} THEN 0 ELSE Max(cs)

(*
 * Read the value for key as seen by transaction txn,
 * if not found, read from the storage,
 * storage is defined on the domain of Key.
 *)
ReadMem(mem, storage, key, txn) ==
    LET idx == FindMem(mem, key, txn)
    IN IF idx = 0
        THEN storage[key]
        ELSE mem[idx][key]

\* Write changes cs for transaction txn to mem.
WriteMem(mem, txn, cs) == [mem EXCEPT ![txn] = cs]

(*
 * returns the visible key value pairs for transaction txn,
 * i.e. the union of all mem[i] for i < txn, with bigger i taking precedence
 * for the same key.
 *)
ViewMem(mem, storage, txn) == [k \in Key |-> ReadMem(mem, storage, k, txn)]

================================================================================
