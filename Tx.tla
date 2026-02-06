---------------------------------- MODULE Tx -----------------------------------
EXTENDS Sequences

CONSTANTS Key, Val, NoVal, BlockSize, Storage

INSTANCE Mem

ASSUME BlockSize > 0
ASSUME Storage \in Dict

VARIABLES mem

TypeOK == TypeOKMem(mem, BlockSize)

Init == mem = EmptyMem(BlockSize)

Next ==
    mem' = Write(mem, 1, [k1 |-> "v2", k2 |-> "v3"])

Spec == Init /\ [][Next]_mem

================================================================================
