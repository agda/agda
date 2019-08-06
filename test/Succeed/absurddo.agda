data ⊥ : Set where

postulate
  M : Set → Set
  A : Set
  _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  ma : M A
  f  : A → M ⊥
  pure : ∀ {A} → A → M A

absurd-do : ∀ {A} → M A
absurd-do = do
  x  ← ma
  () ← f x

atabsurd-do : ∀ {A} → M A
atabsurd-do = do
  x      ← ma
  (y@()) ← f x -- I don't know why you would do that but we can support it
