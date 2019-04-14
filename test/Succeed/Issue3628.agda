{-# OPTIONS --cubical #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Unit

data S : Set where
  base : S

foo : ∀ i j k → Partial _ S
foo i j k (i = i0)(k = i1) = base
foo i j k (j = i1)         = base


-- Testing that fallthrough patterns get expanded when compiling the
-- clauses of foo.
-- Just because (i = i0) matches the first clause doesn't mean we commit to it.
-- `foo i0 i1 k o` should still compute to base by the second clause.
testf : ∀ k (o : IsOne i1) → foo i0 i1 k o ≡ base
testf k o i = base
