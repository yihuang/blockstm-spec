------------------------------- MODULE PartialFn -------------------------------
CONSTANTS Key, Val, NoVal

\* https://discuss.tlapl.us/msg01723.html
PFun(S, T) == UNION {[AS -> T]: AS \in SUBSET S}

Dict == PFun(Key, Val)
Overlay == PFun(Key, Val \union {NoVal})

GetOrNoVal(d, k) ==
    IF k \in DOMAIN d THEN d[k] ELSE NoVal

================================================================================
