---- MODULE MCTx ----

VARIABLES mem, execStatus, incarnation, readSet

CONSTANTS NoVal

Key == {"k1"}
Val == {0, 1, 2, 3, 4, 5}

INSTANCE Tx WITH
    BlockSize <- 5,
    Storage <- [k \in Key |-> 0]

====
