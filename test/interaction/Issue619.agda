
open import Common.Reflection
open import Common.Prelude

data Z : Set where
  zero : Z

foo : QName → Bool → Bool
foo (quote Nat.zero) b = {!b!}
foo _ _ = false
