--------------------------------- MODULE Mem ---------------------------------
EXTENDS Integers

(*
 * Mem is sequence of changesets written by transactions in a block.
 *)

TypeOKMem(mem, blockSize, Key, Val) ==
    /\ Len(mem) = blockSize
    /\ \A i \in 1..blockSize: mem[i] \in [Key -> Val]

Max(s) == CHOOSE i \in s: \A j \in s: j <= i

(*
 * Find the version of key as seen by transaction txn,
 * i.e. the largest index i < txn such that mem[i] contains key,
 * returns 0 if not found in mem.
 *)
Find(mem, key, txn) ==
    LET cs == {i \in 1..(txn - 1): key \in DOMAIN mem[i]} IN
        IF cs = {} THEN 0 ELSE Max(cs)

(*
 * Read the value for key as seen by transaction txn.
 * read from storage if not found in mem.
 *)
Read(mem, storage, key, txn) ==
    LET idx == Find(mem, key, txn) IN
        IF idx = 0 THEN storage[key] ELSE mem[idx][key]

Write(mem, txn, changeset) == [mem EXCEPT ![txn] = changeset]

================================================================================
