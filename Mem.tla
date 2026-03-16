---------------------------------- MODULE Mem ----------------------------------
EXTENDS Sequences, Integers

CONSTANTS Key, Val, NoVal, BlockSize, Storage

ASSUME Storage \in [Key -> Val] \* Initial state

INSTANCE Store

VARIABLE mem

(*
 * Mem is a naive implementation of multi-version memory,
 * where mem[i] is the overlay of changes for transaction i.
 *)

Max(s) == CHOOSE i \in s: \A j \in s: j <= i

TxIndex == 1..BlockSize

InitMem ==
    mem = [i \in TxIndex |-> <<>>]

TypeOKMem ==
    mem \in [TxIndex -> Overlay]

(*
 * Find the version of key as seen by transaction txn,
 * i.e. the largest index i < txn such that mem[i] contains the key,
 * returns 0 if not found.
 *)
FindMem(key, txn) ==
    IF txn <= 1 THEN 0
    ELSE
        LET cs == {i \in 1..(txn - 1): key \in DOMAIN mem[i]} IN
            IF cs = {} THEN 0 ELSE Max(cs)

(*
 * Read the value for key as seen by transaction txn,
 * if not found, read from the Storage,
 * Storage is defined on the domain of Key.
 *)
ReadMem(key, txn) ==
    LET idx == FindMem(key, txn)
    IN IF idx = 0
        THEN Storage[key]
        ELSE mem[idx][key]

\* Write changes cs for transaction txn to mem.
WriteMem(txn, cs) == mem' = [mem EXCEPT ![txn] = cs]

(*
 * returns the visible key value pairs for transaction txn,
 * i.e. the union of all mem[i] for i < txn, with bigger i taking precedence
 * for the same key.
 *)
ViewMem(txn) == [k \in Key |-> ReadMem(k, txn)]

================================================================================
