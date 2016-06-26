
data N : Set where
  suc : N → N

data Val : N → Set where
  valSuc : ∀ n → Val (suc n)

record R : Set where
  constructor wrap
  field unwrap : N

data W (ft : R) : Set where
  immed : (v : Val (R.unwrap ft)) → W ft

test : (fa : R) → W fa → R
test fa (immed (valSuc a)) = fa

postulate
  Evaluate : ∀ (ft : R) (P : (w : W ft) → Set) → Set

test₂ : ∀ (fa : R) → Set
test₂ fa = Evaluate fa testw
  where
  testw : W fa → Set
  testw (immed (valSuc a)) = W fa
