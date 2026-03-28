---------------------------- MODULE MCDependency ----------------------------

EXTENDS Dependency

ASSUME Key # {}

\* Deterministic scenario helpers.
OnlyKey == CHOOSE k \in Key : TRUE

FirstTxn   == 1
SecondTxn  == IF BlockSize >= 2 THEN 2 ELSE 1
LastTxn    == BlockSize
PrevLastTxn == IF BlockSize >= 2 THEN BlockSize - 1 ELSE BlockSize

\* All transactions access no keys (no conflicts possible).
NoConflictKeys == [i \in TxIndex |-> {}]

\* Two transactions share a single key; all others are no-ops.
\* This creates a potential push-abort scenario: if the lower-indexed
\* transaction (txn1) executes AFTER the higher-indexed one (txn2),
\* txn2 must be push-aborted and re-executed.
ConflictScenarioKeys(txn1, txn2) ==
    IF BlockSize >= 2 /\ txn1 # txn2
    THEN [i \in TxIndex |-> IF i \in {txn1, txn2} THEN {OnlyKey} ELSE {}]
    ELSE NoConflictKeys

\* Tail conflict (BlockSize >= 2): PrevLastTxn and LastTxn share a key.
AbortWitnessKeys == ConflictScenarioKeys(PrevLastTxn, LastTxn)

\* Head conflict (BlockSize >= 2): FirstTxn and SecondTxn share a key.
AbortWitnessAltKeys == ConflictScenarioKeys(FirstTxn, SecondTxn)

InitAbortWitness ==
    /\ InitCore
    /\ txKeys = AbortWitnessKeys

InitAbortWitnessAlt ==
    /\ InitCore
    /\ txKeys = AbortWitnessAltKeys

InitNoConflict ==
    /\ InitCore
    /\ txKeys = NoConflictKeys

SpecAbortWitness    == InitAbortWitness    /\ [][Next]_vars /\ WF_vars(Next)
SpecAbortWitnessAlt == InitAbortWitnessAlt /\ [][Next]_vars /\ WF_vars(Next)
SpecNoConflict      == InitNoConflict      /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================
