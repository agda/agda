open import Common.Prelude

instance
  tti : ⊤
  tti = record{}

NonZero : Nat → Set
NonZero zero    = ⊥
NonZero (suc _) = ⊤

pred′ : (n : Nat) .{{_ : NonZero n}} → Nat
pred′ zero {{}}
pred′ (suc n) = n

test : (n : Nat) {{x y : NonZero n}} → Nat
test n = pred′ n

_<_ : Nat → Nat → Set
m < zero = ⊥
zero < suc n = ⊤
suc m < suc n = m < n

instance
  <-suc : ∀ {m n} → .{{_ : m < n}} → m < suc n
  <-suc {zero} = tt
  <-suc {suc m} {zero} {{}}
  <-suc {suc m} {suc n} = <-suc {m} {n}

