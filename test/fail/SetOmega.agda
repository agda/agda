
module SetOmega where

postulate
  IsType : ∀ {a} → Set a → Set
  Bad    : IsType (∀ a → Set a)
