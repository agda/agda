
variable
  X : Set

postulate
  foo : ∀ A -> X   -- error at `src/full/Agda/TypeChecking/Monad/MetaVars.hs:98`
                   -- expected: `{X : Set} -> _1 -> X`
  Y : Set
  bar : ∀ A -> Y   -- normal `_1 -> Y` type with unsolved metavar
