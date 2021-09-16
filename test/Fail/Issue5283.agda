-- Andreas, 2021-08-19, issue #5283, reported by guilhermehas

-- 'tactic' should only appear in attributes and 'C.Tactic' is converted to
-- 'TacticAttribute' there.
-- Other occurrences of 'C.Tactic' should be a scope error.
-- At the time of writing, the scope checker passes it as A.Tactic to the type
-- checker, and that loops on it.

open import Agda.Builtin.Reflection

A : Set
A = tactic ?

-- Should be syntax error.
