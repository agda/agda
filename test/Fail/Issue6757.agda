{-# OPTIONS --cubical #-}
module Issue6757 where

open import Agda.Primitive
open import Agda.Builtin.Cubical.Path

-- Test case due to Matthias Hutzler
--
-- _x in the defn. of test is not an interaction meta, so we shouldn't
-- generate the boundary warning.

refl : {A : Set} → {x : A} → x ≡ x
refl {x = x} i = x

test : {A : Set} → {x y : A} → x ≡ y
test i = refl i
