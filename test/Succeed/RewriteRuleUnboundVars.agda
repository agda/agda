{-# OPTIONS --rewriting #-}

open import Common.Prelude
open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

postulate
  f : Bool → Bool
  boolTrivial : ∀ (b c : Bool) → f b ≡ c

{-# REWRITE boolTrivial #-}

-- Should trigger a warning that c is not bound on the lhs.
