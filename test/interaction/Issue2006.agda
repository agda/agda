-- Andreas, 2016-06-08 issue #2006 (actually #289)

open import Common.Reflection
open import Common.Prelude

bla : Term → Term
bla = {!!}  -- Splitting here should be fine

macro
  comp : Term → Term → TC ⊤
  comp x t = bindTC (quoteTC (bla x)) (λ y → unify t y)

foo : Term
foo = comp Set
