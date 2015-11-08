{-# OPTIONS --exact-split #-}
-- {-# OPTIONS -v tc.cover.splittree:10 #-}

open import Common.Prelude
open import Common.Equality

test : {m n : Nat} → m ≡ n → Nat
test {zero}  refl = zero
test {suc m} refl = suc m
