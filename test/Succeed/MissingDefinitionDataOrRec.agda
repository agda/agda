
data U : Set
T : U -> Set
record V u (t : T u) : Set -- note that u's Set is found by unification
