------------------------------- MODULE Store -------------------------------
CONSTANTS Key, Val, NoVal

\* NoVal == CHOOSE v: v \notin Val

\* https://discuss.tlapl.us/msg01723.html
PFun(S, T) == UNION {[AS -> T]: AS \in SUBSET S}

\* Store is always defined on Key, NoVal is used to represent the absence of a value.
Store == [Key -> Val \cup {NoVal}]

\* Overlay represents changes to a Store, where NoVal means the key is deleted.
Overlay == PFun(Key, Val \union {NoVal})

\* MergeChanges merges two overlays, where the second overlay takes precedence over the first one.
MergeChanges(o1, o2) ==
    [k \in DOMAIN o1 \cup DOMAIN o2 |->
        IF k \in DOMAIN o2 THEN o2[k] ELSE o1[k]]

\* ApplyChanges writes the changes cs to Store.
ApplyChanges(store, cs) == [k \in Key |-> IF k \in DOMAIN cs THEN cs[k] ELSE store[k]]

================================================================================
