module Issue175 where

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN CHAR   Char   #-}
{-# BUILTIN STRING String #-}

primitive primStringToList : String → List Char

lemma : primStringToList "0" ≡ ('0' ∷ [])
lemma = refl
