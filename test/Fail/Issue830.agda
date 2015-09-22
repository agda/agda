--{-# OPTIONS -v tc.data:100 #-}
module Issue830 where

_⟶_ : Set₁ → Set → Set₁
A ⟶ B = A → B

data ⟨Set⟩ : Set where
  [_] : Set ⟶ ⟨Set⟩

-- should fail
