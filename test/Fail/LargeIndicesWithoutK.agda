{-# OPTIONS --cubical-compatible #-}
-- Large indices are not allowed --cubical-compatible

data Singleton {a} {A : Set a} : A → Set where
  [_] : ∀ x → Singleton x
