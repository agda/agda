module Common.IO where

open import Common.Bool
open import Common.Char
open import Common.Nat
open import Common.String
open import Common.Unit
open import Common.Float

postulate
  IO : ∀ {l} → Set l → Set l

{-# BUILTIN IO IO #-}

-- MAlonzo
{-# IMPORT Common.FFI #-}
{-# COMPILED_TYPE IO Common.FFI.AgdaIO #-}

infixl 1 _>>=_

postulate
  return  : ∀ {a} {A : Set a} → A → IO A
  _>>=_   : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILED return (\_ _ -> return) #-}
{-# COMPILED _>>=_ (\_ _ _ _ -> (>>=)) #-}
{-# COMPILED_EPIC return (u1 : Unit, a : Any) -> Any = ioreturn(a) #-}
{-# COMPILED_EPIC _>>=_ (u1 : Unit, u2 : Unit, x : Any, f : Any) -> Any = iobind(x,f) #-}
{-# COMPILED_UHC return (\_ _ x -> UHC.Agda.Builtins.primReturn x) #-}
{-# COMPILED_UHC _>>=_ (\_ _ _ _ x y -> UHC.Agda.Builtins.primBind x y) #-}


{-# IMPORT Data.Text.IO #-}

postulate
  putStr     : String -> IO Unit

{-# COMPILED putStr Data.Text.IO.putStr #-}
{-# COMPILED_EPIC putStr (a : String, u : Unit) -> Unit = foreign Int "wputStr" (a : String); primUnit #-}
{-# COMPILED_UHC putStr (UHC.Agda.Builtins.primPutStr) #-}


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
