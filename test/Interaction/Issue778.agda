-- {-# OPTIONS -v tc.term.exlam:100 -v extendedlambda:100 -v int2abs.reifyterm:100 #-}
-- Andreas, 2013-02-26
module Issue778 (Param : Set) where

data ⊥ : Set where

interactive : ⊥ → ⊥
interactive = λ {x → {!x!}}
  where aux : ⊥ → ⊥
        aux x = x

-- splitting did not work for extended lambda in the presence of
-- module parameters and where block

data ⊤ : Set where
  tt : ⊤

test : ⊤ → ⊤
test = λ { x → {!x!} }
  where aux : ⊤ → ⊤
        aux x = x
