{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality

postulate
  A : Set
  x0 : A
  f : A → A → A

{-# BUILTIN REWRITE _≡_ #-}

postulate
  fxx : (x : A) → (f x x) ≡ x

{-# REWRITE fxx #-}

meta : A
meta-reveal : meta ≡ x0
test : f x0 meta ≡ x0

meta = _
test = refl
meta-reveal = refl
