module Issue1494.Helper where

record Record : Set₁ where
  field _≡_ : {A : Set} → A → A → Set

module Module (r : Record) where

  open Record r public
