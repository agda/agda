-- Andreas, 2018-09-07 issue #3217 reported by Nisse
--
-- Missing range for cubical error

{-# OPTIONS --cubical #-}

-- {-# OPTIONS -v tc.term.lambda:100 -v tc.term:10 #-}

open import Agda.Builtin.Cubical.Path

data Bool : Set where
  true false : Bool

eq : true ≡ false
eq = λ i → true

-- Expected error
-- Issue3217.agda:15,12-16
-- true != false of type Bool
-- when checking that the expression λ i → true has type true ≡ false
