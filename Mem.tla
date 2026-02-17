---------------------------------- MODULE Mem ----------------------------------
EXTENDS Sequences, Integers, FiniteSetsExt

CONSTANTS Key, Val, NoVal, BlockSize

INSTANCE PartialFn

(*
 * Mem is sequence of changesets written by transactions in a block.
 *)

TxIndex == 1..BlockSize

EmptyMem ==
    [i \in TxIndex |-> <<>>]

TypeOKMem(mem) ==
    mem \in [TxIndex -> Overlay]

(*
 * find the version of key as seen by transaction txn,
 * i.e. the largest index i < txn such that mem[i] contains key,
 * returns 0 if not found in mem.
 *)
FindMem(mem, key, txn) ==
    LET cs == {i \in 1..(txn - 1): key \in DOMAIN mem[i]} IN
        IF cs = {} THEN 0 ELSE Max(cs)

(*
 * Read the value for key as seen by transaction txn.
 * read from storage if not found in mem.
 *
 * Storage is assumed to be defined on all keys, non-existence can be
 * represented by NoVal.
 *)
ReadMem(mem, storage, key, txn) ==
    LET idx == FindMem(mem, key, txn)
    IN IF idx = 0
        THEN GetOrNoVal(storage, key)
        ELSE mem[idx][key]

WriteMem(mem, txn, cs) == [mem EXCEPT ![txn] = cs]

(*
 * returns the visible key value pairs for transaction txn,
 * i.e. the union of all mem[i] for i < txn, with bigger i taking precedence
 * for the same key.
 *)
ViewMem(mem, storage, txn) ==
    ToDict([k \in Key |-> ReadMem(mem, storage, k, txn)])


================================================================================
