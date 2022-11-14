{-# OPTIONS --cubical-compatible #-}
module Issue6298 where

open import Agda.Builtin.Equality

-- Fails because the A argument is used to compute the transport of P
-- along the path representing eq. The x argument is forced to be y, so
-- the fact that *it* is erased does not matter.
J : ∀ (@0 A : Set) (@0 x : A) (P : (y : A) → x ≡ y → Set) → (prefl : P x refl) → (y : A) (eq : x ≡ y) → P y eq
J A xyz P prefl x refl = prefl
