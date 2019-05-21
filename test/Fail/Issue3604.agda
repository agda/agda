data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

data Is-nothing {A} : Maybe A → Set where
  nothing : Is-nothing nothing

record ℕ∞ : Set where
  coinductive
  field
    prd∞ : Maybe ℕ∞

open ℕ∞

f :  ℕ∞ → ℕ∞
prd∞ (f m) with prd∞ m
prd∞ (f m) | just pm with f pm
prd∞ (f m) | just pm | x = prd∞ x
prd∞ (f m) | nothing = nothing

inf∞ : ℕ∞
prd∞ inf∞ = just inf∞

test : Is-nothing (prd∞ (f inf∞))
test = nothing
