-- Andreas, 2018-10-15, issue #3262 reported by Guillaume Brunerie
--
-- Missing with clauses should be reported close to problem location
-- not just at the type signature of the function which has this problem.

data T : Set where
  a b c : T

f : T → Set
f a = ?
f b = ?
f c with c | c
... | _ = ?

-- Should trigger the "missing with clauses" error
-- at the lhs with the "with".
