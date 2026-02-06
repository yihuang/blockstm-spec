---------------------------------- MODULE Tx -----------------------------------
EXTENDS Sequences, TLC

CONSTANTS Key, Val, NoVal, BlockSize, Storage

INSTANCE Mem

ASSUME BlockSize > 0
ASSUME Storage \in Dict
ASSUME Val \subseteq Nat

VARIABLES mem, txKey, txStatus, txObserved

vars == <<mem, txKey, txStatus, txObserved>>

TxIndex == 1..BlockSize

TypeOK ==
    /\ TypeOKMem(mem, BlockSize)
    /\ txStatus \in [TxIndex -> {"read", "write", "done"}]
    /\ txKey \in [TxIndex -> Key]
    /\ txObserved \in [TxIndex -> Nat]

Init ==
    /\ mem = EmptyMem(BlockSize)
    /\ txStatus = [i \in TxIndex |-> "read"]
    /\ txObserved = [i \in TxIndex |-> 0]
    /\ txKey \in [TxIndex -> Key]

ReadOrZero(txn) ==
    LET val == Read(mem, Storage, txKey[txn], txn)
    IN IF val = NoVal
        THEN 0
        ELSE val

TxRead(txn) ==
    /\ txStatus[txn] = "read"
    /\ txStatus' = [txStatus EXCEPT ![txn] = "write"]
    /\ txObserved' = [txObserved EXCEPT ![txn] = ReadOrZero(txn)]
    /\ UNCHANGED <<mem, txKey>>

TxWrite(txn) ==
    /\ txStatus[txn] = "write"
    /\ txStatus' = [txStatus EXCEPT ![txn] = "done"]
    /\ LET cs == txKey[txn] :> txObserved[txn] + 1 IN 
        mem' = Write(mem, txn, cs)
    /\ UNCHANGED <<txKey, txObserved>>

TxDone(txn) ==
    /\ txStatus[txn] = "done"
    /\ UNCHANGED vars

Next ==
    \E txn \in TxIndex:
        TxRead(txn) \/ TxWrite(txn) \/ TxDone(txn)

Spec == Init /\ [][Next]_vars

================================================================================
