-------------------------------- MODULE MCTx --------------------------------
EXTENDS Tx

ASSUME Key # {}

\* Deterministic scenario helpers.
OnlyKey == CHOOSE k \in Key : TRUE
NoopTx == [reads |-> {}, writes |-> {}, deps |-> <<>>]
WriteOneTx == [reads |-> {}, writes |-> {OnlyKey}, deps |-> (OnlyKey :> {})]
ReadThenWriteOneTx == [reads |-> {OnlyKey}, writes |-> {OnlyKey}, deps |-> (OnlyKey :> {OnlyKey})]
NoopBlock == [i \in TxIndex |-> NoopTx]

FirstTxn == 1
SecondTxn == IF BlockSize >= 2 THEN 2 ELSE 1
LastTxn == BlockSize
PrevLastTxn == IF BlockSize >= 2 THEN BlockSize - 1 ELSE BlockSize

ConflictScenarioBlock(writeTxn, readWriteTxn) ==
	IF BlockSize >= 2 /\ writeTxn # readWriteTxn
	THEN [NoopBlock EXCEPT
		![writeTxn] = WriteOneTx,
		![readWriteTxn] = ReadThenWriteOneTx]
	ELSE NoopBlock

\* Tail conflict (BlockSize >= 2): TxExecute(LastTxn) -> TxExecute(PrevLastTxn) -> TxValidateAbort(LastTxn)
AbortWitnessBlock == ConflictScenarioBlock(PrevLastTxn, LastTxn)

\* Head conflict (BlockSize >= 2): TxExecute(SecondTxn) -> TxExecute(FirstTxn) -> TxValidateAbort(SecondTxn)
AbortWitnessAltBlock == ConflictScenarioBlock(FirstTxn, SecondTxn)

\* Commit-friendly: all tx are no-ops, so commits can progress quickly.
CommitFriendlyBlock == NoopBlock

InitAbortWitness ==
	/\ Key # {}
	/\ InitCore
	/\ block = AbortWitnessBlock

InitAbortWitnessAlt ==
	/\ Key # {}
	/\ InitCore
	/\ block = AbortWitnessAltBlock

InitCommitFriendly ==
	/\ Key # {}
	/\ InitCore
	/\ block = CommitFriendlyBlock

SpecAbortWitness == InitAbortWitness /\ [][Next]_vars /\ WF_vars(Next)
SpecAbortWitnessAlt == InitAbortWitnessAlt /\ [][Next]_vars /\ WF_vars(Next)
SpecCommitFriendly == InitCommitFriendly /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================
