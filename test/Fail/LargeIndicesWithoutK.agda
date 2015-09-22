{-# OPTIONS --without-K #-}
-- Large indices are not allowed --without-K

data Singleton {a} {A : Set a} : A → Set where
  [_] : ∀ x → Singleton x
