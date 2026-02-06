---- MODULE MCTx ----

VARIABLES mem

CONSTANTS NoVal

Key == {"k1", "k2", "k3"}
Val == {"v1", "v2", "v3"}

INSTANCE Tx WITH
    BlockSize <- 5,
    Storage <- [k \in Key |-> NoVal]

====
