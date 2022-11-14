{-# OPTIONS --cubical --rewriting #-}
open import Agda.Builtin.Cubical.Path using (_≡_)
{-# BUILTIN REWRITE _≡_ #-}

record ⊤ : Set where
  constructor tt

postulate foo : tt ≡ tt → ⊤
postulate bar : foo (λ _ → tt) ≡ tt
{-# REWRITE bar #-}
