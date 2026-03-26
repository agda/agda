{-# OPTIONS --cubical --rewriting #-}
open import Agda.Builtin.Cubical.Path using (PathP; _≡_)
{-# BUILTIN REWRITE PathP #-}

record ⊤ : Set where
  constructor tt

postulate foo : tt ≡ tt → ⊤
postulate bar : foo (λ _ → tt) ≡ tt
{-# REWRITE bar #-}
