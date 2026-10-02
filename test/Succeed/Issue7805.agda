module Issue7805 where

record X : Set₁ where
  field
    it : {A : Set} → A → A

_ = record where it x = x
