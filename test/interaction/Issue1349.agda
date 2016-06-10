-- Andreas, fixed #1349 on 2016-06-08

-- {-# OPTIONS -v tc.term.exlam:50 -v scope.extendedLambda:10 #-}

module Issue1349 where

open import Common.Prelude

module Logic {s} (F : Set s) (arF : F → Nat) where

  data Term : Nat → Set s where
    var : ∀ n → Term (suc n)

d : Unit → Nat
d = \ {unit → zero}  -- fails
-- d unit = zero     -- works

module M = Logic Unit d -- (λ{unit -> zero})

test : Logic.Term Unit {!!} (suc zero)
test = M.var zero

-- WAS:
-- Agda2> Ambiguous name: Issue1349._..extendedlambda0
-- (agda2-info-action "*Error*" "An internal error has occurred. Please report this as a bug. Location of the error: src/full/Agda/TypeChecking/Reduce/Monad.hs:172" nil)

-- Gives proper error now.
