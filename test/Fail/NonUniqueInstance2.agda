open import Common.Prelude hiding (tt)

instance
  tt : ⊤
  tt = record{}

_<_ : Nat → Nat → Set
m < zero = ⊥
zero < suc n = ⊤
suc m < suc n = m < n

instance
  <-suc : ∀ {m n} {{_ : m < n}} → m < suc n
  <-suc {zero} = tt
  <-suc {suc m} {zero} {{}}
  <-suc {suc m} {suc n} = <-suc {m} {n}

