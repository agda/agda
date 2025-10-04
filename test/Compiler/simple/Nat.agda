open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

postulate
  putStrLn : String → IO ⊤
  _>>_ : {A B : Set} → IO A → IO B → IO B

infixl 1 _>>_

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC _>>_ = \ _ _ -> (>>) #-}
{-# COMPILE JS putStrLn = x => y => (console.log(x), y) #-}
{-# COMPILE JS _>>_ = _ => _ => x => y => z => y(x(z)) #-}
-- {-# COMPILE JS putStrLn = x => console.log(x) #-}
-- {-# COMPILE JS _>>_ = _ => _ => x => y => y #-}

infixl 6 _++_

_++_ : String → String → String
_++_ = primStringAppend

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

assertEq : String → Nat → Nat → IO ⊤
assertEq s x y =
  if x == y then
    putStrLn (s ++ " PASSED: " ++ primShowNat x ++ " == " ++ primShowNat y)
  else
    putStrLn (s ++ " FAILED: " ++ primShowNat x ++ " != " ++ primShowNat y)

test-helper : (k m n j q r : Nat) → IO ⊤
test-helper k m n j q r =
  assertEq ("div-helper " ++ primShowNat k ++ " " ++ primShowNat m ++ " " ++ primShowNat n ++ " " ++ primShowNat j ++ " == " ++ primShowNat q)
           (div-helper k m n j) q >>
  assertEq ("mod-helper " ++ primShowNat k ++ " " ++ primShowNat m ++ " " ++ primShowNat n ++ " " ++ primShowNat j ++ " == " ++ primShowNat r)
           (mod-helper k m n j) r

data ⊥ : Set where

NonZero : Nat → Set
NonZero 0 = ⊥
NonZero _ = ⊤

instance
  nonZero : ∀ {n} → NonZero (suc n)
  nonZero = _

_/_ : (dividend divisor : Nat) .{{_ : NonZero divisor}} → Nat
m / (suc n) = div-helper 0 n m n

_%_ : (dividend divisor : Nat) .{{_ : NonZero divisor}} → Nat
m % (suc n) = mod-helper 0 n m n

test : (m n q r : Nat) .{{_ : NonZero n}} → IO ⊤
test m n q r =
  assertEq (primShowNat m ++ " / " ++ primShowNat n ++ " == " ++ primShowNat q)
           (m / n) q >>
  assertEq (primShowNat m ++ " % " ++ primShowNat n ++ " == " ++ primShowNat r)
           (m % n) r

main : IO ⊤
main = do
  test-helper 0 0 0 0 0 0
  test-helper 0 0 0 1 0 0
  test-helper 0 0 0 2 0 0
  test-helper 0 0 1 0 1 0
  test-helper 0 0 1 1 0 1
  test-helper 0 0 1 2 0 1
  test-helper 0 0 2 0 2 0
  test-helper 0 0 2 1 1 0
  test-helper 0 0 2 2 0 2
  test-helper 0 1 0 0 0 0
  test-helper 0 1 0 1 0 0
  test-helper 0 1 0 2 0 0
  test-helper 0 1 1 0 1 0
  test-helper 0 1 1 1 0 1
  test-helper 0 1 1 2 0 1
  test-helper 0 1 2 0 1 1
  test-helper 0 1 2 1 1 0
  test-helper 0 1 2 2 0 2
  test-helper 0 0 0 0 0 0
  test-helper 1 0 0 1 1 1
  test-helper 1 0 0 2 1 1
  test-helper 1 0 1 0 2 0
  test-helper 1 0 1 1 1 2
  test-helper 1 0 1 2 1 2
  test-helper 1 0 2 0 3 0
  test-helper 1 0 2 1 2 0
  test-helper 1 0 2 2 1 3
  test-helper 1 1 0 0 1 1
  test-helper 1 1 0 1 1 1
  test-helper 1 1 0 2 1 1
  test-helper 1 1 1 0 2 0
  test-helper 1 1 1 1 1 2
  test-helper 1 1 1 2 1 2
  test-helper 1 1 2 0 2 1
  test-helper 1 1 2 1 2 0
  test-helper 1 1 2 2 1 3

  test 0 1 0 0
  test 1 1 1 0
  test 2 1 2 0
  test 3 1 3 0
  test 4 1 4 0
  test 5 1 5 0
  test 6 1 6 0
  test 7 1 7 0
  test 8 1 8 0

  test 0 2 0 0
  test 1 2 0 1
  test 2 2 1 0
  test 3 2 1 1
  test 4 2 2 0
  test 5 2 2 1
  test 6 2 3 0
  test 7 2 3 1
  test 8 2 4 0

  test 0 3 0 0
  test 1 3 0 1
  test 2 3 0 2
  test 3 3 1 0
  test 4 3 1 1
  test 5 3 1 2
  test 6 3 2 0
  test 7 3 2 1
  test 8 3 2 2

  test 0 4 0 0
  test 1 4 0 1
  test 2 4 0 2
  test 3 4 0 3
  test 4 4 1 0
  test 5 4 1 1
  test 6 4 1 2
  test 7 4 1 3
  test 8 4 2 0
