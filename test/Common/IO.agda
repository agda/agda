{-# OPTIONS --without-K #-}
module Common.IO where

open import Agda.Builtin.IO public
open import Common.Bool
open import Common.Char
open import Common.Nat
open import Common.String
open import Common.Unit
open import Common.Float

infixl 1 _>>=_

postulate
  return  : ∀ {a} {A : Set a} → A → IO A
  _>>=_   : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC return = \_ _ -> return #-}
{-# COMPILE GHC _>>=_ = \_ _ _ _ -> (>>=) #-}
{-# COMPILE UHC return = \_ _ x -> UHC.Agda.Builtins.primReturn x #-}
{-# COMPILE UHC _>>=_ = \_ _ _ _ x y -> UHC.Agda.Builtins.primBind x y #-}
{-# COMPILE JS return =
    function(u0) { return function(u1) { return function(x) { return function(cb) { cb(x); }; }; }; } #-}
{-# COMPILE JS _>>=_ =
  function(u0) { return function(u1) { return function(u2) { return function(u3) {
    return function(x) { return function(y) { return function(cb) {
      x(function (xx) { y(xx)(cb); });
  }; }; };
  }; }; }; }
#-}

{-# FOREIGN GHC import qualified Data.Text.IO #-}

postulate
  putStr     : String -> IO Unit

{-# COMPILE GHC putStr = Data.Text.IO.putStr #-}
{-# COMPILE UHC putStr = UHC.Agda.Builtins.primPutStr #-}
{-# COMPILE JS putStr = function (x) { return function(cb) { process.stdout.write(x); cb(0); }; } #-}


printChar : Char -> IO Unit
printChar c = putStr (charToStr c)

putStrLn   : String -> IO Unit
putStrLn s = putStr s >>= \_ -> putStr "\n"

printNat : Nat -> IO Unit
printNat n = putStr (natToString n)

printBool : Bool -> IO Unit
printBool true = putStr "true"
printBool false = putStr "false"

printFloat : Float -> IO Unit
printFloat f = putStr (floatToString f)

infixr 2 _<$>_
_<$>_ : {A B : Set}(f : A -> B)(m : IO A) -> IO B
f <$> x = x >>= λ y -> return (f y)

infixr 0 bind
bind : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B
bind m f = m >>= f

infixr 0 then
then : ∀ {a b} {A : Set a} {B : Set b} -> IO A -> IO B -> IO B
then m f = m >>= λ _ -> f

syntax bind e (\ x -> f) = x <- e , f
syntax then e f          = e ,, f
