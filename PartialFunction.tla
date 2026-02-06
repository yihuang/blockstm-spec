---------------------------- MODULE PartialFunction ----------------------------
CONSTANTS Key, Val, NoVal

IsPartialFunction(f) == f \in [Key -> Val \cup {NoVal}]

================================================================================
