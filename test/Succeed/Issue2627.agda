{-# OPTIONS --allow-unsolved-metas #-}

data ⊤ : Set where
  tt : ⊤

data _≡_ (a : ⊤) : {B : Set} → B → Set where
  refl : a ≡ a

foo : ⊤
foo = (λ (z : ⊤) (q : bar ≡ {!!}) → tt) bar refl
  where
    bar : ⊤
    bar = {!!}
