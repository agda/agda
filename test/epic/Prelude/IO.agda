module Prelude.IO where

open import Prelude.Bool
open import Prelude.Char
open import Prelude.Nat
open import Prelude.String
open import Prelude.Unit
open import Prelude.Vec
open import Prelude.Float

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}

infixl 1 _>>=_

postulate
  return  : ∀ {A} → A → IO A
  _>>=_   : ∀ {A B} → IO A → (A → IO B) → IO B
  numArgs : Nat
  getArg  : Nat -> String

args : Vec String numArgs
args = buildArgs numArgs
  where
    buildArgs : (n : Nat) -> Vec String n
    buildArgs Z     = []
    buildArgs (S n) = snoc (buildArgs n) (getArg n)

{-# COMPILED_EPIC return (u1 : Unit, a : Any) -> Any = ioreturn(a) #-}
{-# COMPILED_EPIC _>>=_ (u1 : Unit, u2 : Unit, x : Any, f : Any) -> Any = iobind(x,f) #-}
{-# COMPILED_EPIC numArgs () -> BigInt = foreign BigInt "numArgsBig" () #-}
{-# COMPILED_EPIC getArg  (n : BigInt) -> Any = foreign Any "getArgBig" (n : BigInt) #-} 

postulate
  natToString : Nat -> String
  readNat    : IO Nat
  readStr    : IO String
  putStr     : String -> IO Unit
  printChar  : Char   -> IO Unit


putStrLn   : String -> IO Unit
putStrLn s = putStr s >>= \_ -> putStr "\n"

printFloat : Float  -> IO Unit
printFloat f = putStr (floatToString f)

printNat : Nat -> IO Unit
printNat n = putStr (natToString n)

printBool : Bool -> IO Unit
printBool true = putStr "true"
printBool false = putStr "false"

{-# COMPILED_EPIC natToString (n : Any) -> String = bigToStr(n) #-}
{-# COMPILED_EPIC readNat (u : Unit) -> Any = strToBig(readStr(u)) #-}

{-# COMPILED_EPIC putStr (a : String, u : Unit) -> Unit = foreign Int "wputStr" (a : String); primUnit #-}
-- {-# COMPILED_EPIC putStrLn (a : String, u : Unit) -> Unit = putStrLn (a) #-}
{-# COMPILED_EPIC readStr (u : Unit) -> Data = readStr(u) #-}
{-# COMPILED_EPIC printChar (c : Int, u : Unit) -> Unit = printChar(c) #-}

infixr 2 _<$>_
_<$>_ : {A B : Set}(f : A -> B)(m : IO A) -> IO B
f <$> x = x >>= λ y -> return (f y)

infixr 0 bind
bind : ∀ {A B} → IO A → (A → IO B) → IO B
bind m f = m >>= f

infixr 0 then
then : ∀ {A B} -> IO A -> IO B -> IO B
then m f = m >>= λ _ -> f

syntax bind e (\ x -> f) = x <- e , f
syntax then e f          = e ,, f