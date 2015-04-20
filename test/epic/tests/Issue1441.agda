-- Moved from the successfull test-suite. See Issue 1481.

module tests.Issue1441 where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

data Unit : Set where
  unit : Unit

postulate
  IO          : Set → Set
  String      : Set
  natToString : Nat → String
  putStr      : String → IO Unit

printNat : Nat → IO Unit
printNat n = putStr (natToString n)

{-# COMPILED_TYPE IO IO #-}

{-# COMPILED_EPIC natToString (n : Any) -> String = bigToStr(n) #-}

{-# COMPILED_EPIC putStr (a : String, u : Unit) ->
                         Unit = foreign Int "wputStr" (a : String); primUnit #-}

data Sing : (n : Nat) → Set where
  sing : ∀ n → Sing n

data D : Set → Set where
  c : ∀ n → D (Sing n)

test : (A : Set) → D A → Nat
test .(Sing n) (c n) = n

main : IO Unit
main = printNat (test (Sing 1) (c 1))

-- should succeed and print 1
