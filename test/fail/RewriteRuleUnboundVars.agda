open import Common.Prelude
open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

postulate
  boolTrivial : ∀ (b c : Bool) → b ≡ c

{-# REWRITE boolTrivial #-}

-- Should trigger an error that c is not bound on the lhs.
