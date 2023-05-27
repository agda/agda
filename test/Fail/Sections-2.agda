{-# OPTIONS -vtc.error:666 -verror:20 -vtc.term:30 #-}
open import Common.Prelude

postulate
  foo_bar_ : (b : Bool) → if b then Nat else Bool → Set

Test : Set
Test = foo_bar 5
