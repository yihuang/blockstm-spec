---- MODULE MCTx ----

VARIABLES mem, txKey, txStatus, txObserved

CONSTANTS NoVal

Key == {"k1", "k2", "k3"}
Val == {0, 1, 2, 3, 4, 5}

INSTANCE Tx WITH
    BlockSize <- 5,
    Storage <- [k \in Key |-> NoVal]

====
