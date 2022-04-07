{-# OPTIONS --cubical-compatible #-}
module _ where

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}  -- This should trigger a warning!
