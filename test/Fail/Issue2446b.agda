{-# OPTIONS --cubical #-}
module _ where

open import Agda.Builtin.Equality

-- Option --cubical implies --without-K
uip : {A : Set} {x : A} (p : x ≡ x) → p ≡ refl
uip refl = refl
