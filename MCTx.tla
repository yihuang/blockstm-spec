-------------------------------- MODULE MCTx --------------------------------
EXTENDS Tx

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

\* Tail conflict: TxExecute(LastTxn) -> TxExecute(PrevLastTxn) -> TxValidateAbort(LastTxn)
AbortWitnessBlock == ConflictScenarioBlock(PrevLastTxn, LastTxn)

\* Head conflict: TxExecute(SecondTxn) -> TxExecute(FirstTxn) -> TxValidateAbort(SecondTxn)
AbortWitnessAltBlock == ConflictScenarioBlock(FirstTxn, SecondTxn)

\* Commit-friendly: all tx are no-ops, so commits can progress quickly.
CommitFriendlyBlock == NoopBlock

InitAbortWitness ==
	/\ InitCore
	/\ block = AbortWitnessBlock

InitAbortWitnessAlt ==
	/\ InitCore
	/\ block = AbortWitnessAltBlock

InitCommitFriendly ==
	/\ InitCore
	/\ block = CommitFriendlyBlock

SpecAbortWitness == InitAbortWitness /\ [][Next]_vars /\ WF_vars(Next)
SpecAbortWitnessAlt == InitAbortWitnessAlt /\ [][Next]_vars /\ WF_vars(Next)
SpecCommitFriendly == InitCommitFriendly /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================
