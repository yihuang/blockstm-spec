---------------------------------- MODULE Tx -----------------------------------
EXTENDS Sequences

CONSTANTS Key, Val, NoVal, BlockSize, Storage

INSTANCE Mem

ASSUME BlockSize > 0
ASSUME IsPartialFunction(Storage)

VARIABLES mem

TypeOK == TypeOKMem(mem, BlockSize)

Init == mem = InitMem(BlockSize)

Next ==
    mem' = Write(mem, 1, [k1 |-> "v2", k2 |-> "v3"])

Spec == Init /\ [][Next]_mem

================================================================================
