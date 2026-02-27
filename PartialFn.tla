------------------------------- MODULE PartialFn -------------------------------
CONSTANTS Key, Val, NoVal

\* NoVal == CHOOSE v: v \notin Val

\* https://discuss.tlapl.us/msg01723.html
PFun(S, T) ≜ UNION {[AS → T]: AS ∈ SUBSET S}

(* A dict is a partial function from keys to values. It can be used to represent the state of storage.
 * The domain of the dict is the set of keys that have values.
 *)
Dict ≜ PFun(Key, Val)

(* Overlay is a partial function that can be used to represent changes to a dict.
 * It maps keys to either values or NoVal, where NoVal represents deletion of the key.
 *)
Overlay ≜ PFun(Key, Val ∪ {NoVal})

(* ToDict convert an Overlay to a Dict by removing all keys that are mapped to NoVal. *)
ToDict(o) ≜
    LET keys ≜ {k ∈ DOMAIN o: o[k] ≠ NoVal}
    IN [k ∈ keys ↦ o[k]]

(* GetOrNoVal returns the value for key k in dict d, or NoVal if k is not in the domain of d. *)
GetOrNoVal(d, k) ≜
    IF k ∈ DOMAIN d THEN d[k] ELSE NoVal

(* ApplyOverlay writes the overlay o into dict d, returning a new dict (without NoVal).
 *)
ApplyOverlay(d, o) ≜
    \* the domain of result is domain d substract the keys in o that are mapped to NoVal,
    \* union the keys in o that are mapped to values.
    LET delKeys ≜ {k ∈ DOMAIN o: o[k] = NoVal}
        addKeys ≜ {k ∈ DOMAIN o: o[k] ≠ NoVal}
        keys ≜ ((DOMAIN d) \ delKeys) ∪ addKeys
    IN [k ∈ keys ↦ IF k ∈ addKeys THEN o[k] ELSE d[k]]

================================================================================
