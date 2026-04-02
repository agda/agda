{-# OPTIONS --erasure #-}

open import Agda.Builtin.Equality

primitive
  primEraseEquality : ∀ {@0 a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
