open import Common.Prelude

instance
  tt : ⊤
  tt = record{}

NonZero : Nat → Set
NonZero zero    = ⊥
NonZero (suc _) = ⊤

pred′ : (n : Nat) {{_ : NonZero n}} → Nat
pred′ zero {{}}
pred′ (suc n) = n

test : (n : Nat) {{x y : NonZero n}} → Nat
test n = pred′ n
