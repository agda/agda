module _ {A : Set} (P : A → Set) where

  instance
   postulate
    forbidden : {x : A} → P x
