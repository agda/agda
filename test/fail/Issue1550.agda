open import Common.Prelude
open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

foo : ∀ x → x + 0 ≡ x
foo zero = refl
foo (suc x) = cong suc (foo x)

{-# REWRITE foo #-}
