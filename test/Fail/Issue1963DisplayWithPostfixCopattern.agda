{-# OPTIONS -v tc.with.display:30 #-}
-- {-# OPTIONS -v tc.with.strip:30 #-}

open import Common.Product
open import Common.Prelude
open import Common.Equality

postulate
  p : Nat → Nat

-- g : Nat → Nat × Nat
-- g x .proj₁ with p x
-- g x .proj₁ | 0 = 1
-- g x .proj₁ | suc y = 0
-- g x .proj₂ = suc x

-- h : Nat → Nat × Nat
-- h x .proj₁ with p x
-- h x .proj₁ | 0 = 1
-- proj₁ (h x) | suc y = 0
-- h x .proj₂ = suc x

f : Nat → Nat × Nat
f x .proj₁ with p x
... | 0 = 1
... | suc y = 0
f x .proj₂ = suc x

test : f 0 ≡ (0 , 1)
test = refl

-- EXPECTED ERROR:
-- f 0 .proj₁ | p 0 != zero of type Nat
-- when checking that the expression refl has type f 0 ≡ (0 , 1)
