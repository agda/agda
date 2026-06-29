{-# OPTIONS --cubical --guardedness #-}
{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Equality renaming (_≡_ to _≡ᴵ_; refl to reflᴵ)
import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical using (I)
open import Agda.Builtin.Nat

postulate
  foo : Nat → Nat

bar : Nat → Nat → Nat
bar zero    m = m
bar (suc n) m = m

test1 : (n : Nat) → bar (foo n) ≡ (λ m → m)
test1 n i m with foo n
... | suc _ = m
... | zero  = m
