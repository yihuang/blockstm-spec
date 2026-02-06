------------------------------- MODULE PartialFn -------------------------------
CONSTANTS Key, Val, NoVal

\* https://discuss.tlapl.us/msg01723.html
PFun(S, T) == UNION {[AS -> T]: AS \in SUBSET S}

(* A dict is a partial function from keys to values. It can be used to represent the state of storage.
 * The domain of the dict is the set of keys that have values.
 *)
Dict == PFun(Key, Val)

(* Overlay is a partial function that can be used to represent changes to a dict.
 * It maps keys to either values or NoVal, where NoVal represents deletion of the key.
 *)
Overlay == PFun(Key, Val \union {NoVal})

(* GetOrNoVal returns the value for key k in dict d, or NoVal if k is not in the domain of d. *)
GetOrNoVal(d, k) ==
    IF k \in DOMAIN d THEN d[k] ELSE NoVal

================================================================================
