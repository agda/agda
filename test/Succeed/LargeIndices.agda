{-# OPTIONS --large-indices #-}
-- Forced constructor arguments don't count towards the size of the datatype
-- (only if not --withoutK).

data _≡_ {a} {A : Set a} : A → A → Set where
  refl : ∀ x → x ≡ x

data Singleton {a} {A : Set a} : A → Set where
  [_] : ∀ x → Singleton x
