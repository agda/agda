module Issue857 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim = λ ()

bad : (x : ⊥) → ⊥-elim x ≡ tt
bad x = {!!}  -- Goal type: x ≡ tt, with x : ⊥.
