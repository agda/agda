{-# OPTIONS -v treeless.opt:20 #-}
module _ where

open import Agda.Builtin.Nat renaming (_<_ to _<?_)
open import Common.Prelude
open import Common.Equality
open import Agda.Builtin.TrustMe

data _<_ (a b : Nat) : Set where
  diff : (k : Nat) → b ≡ suc k + a → a < b

data Comparison {a} {A : Set a} (_<_ : A → A → Set a) (x y : A) : Set a where
  less    : x < y → Comparison _<_ x y
  equal   : x ≡ y → Comparison _<_ x y
  greater : y < x → Comparison _<_ x y

compare : (a b : Nat) → Comparison _<_ a b
compare a b with a <? b
... | true  = less (diff (b ∸ suc a) primTrustMe)
... | false with b <? a
...   | true  = greater (diff (a ∸ suc b) primTrustMe)
...   | false = equal primTrustMe

{-# INLINE compare #-}

-- This should compile to two calls of _<?_ and only the possible cases.
compare-lots : (a b : Nat) → String
compare-lots a b with compare a b | compare (suc a) (suc b)
compare-lots a b | less (diff k eq) | less (diff k₁ eq₁) = "less-less"
compare-lots a .a | less (diff k eq) | equal refl = "less-equal"
compare-lots a _ | less (diff k refl) | greater (diff j eq) = "less-greater"
compare-lots a .a | equal refl | less (diff k eq₁) = "equal-less"
compare-lots a b | equal eq | equal eq₁ = "equal-equal"
compare-lots a .a | equal refl | greater (diff k eq₁) = "equal-greater"
compare-lots _ b | greater (diff k refl) | less (diff j eq) = "greater-less"
compare-lots _ b | greater (diff k refl) | equal eq = "greater-equal"
compare-lots a b | greater (diff k eq) | greater (diff k₁ eq₁) = "greater-greater"

main : IO Unit
main = putStrLn (compare-lots 1500 2000) ,,
       putStrLn (compare-lots 2000 1500) ,,
       putStrLn (compare-lots 2000 2000)
