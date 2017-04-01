-- Andreas, 2017-03-30, issue #2524
-- compile abstract definitions to arbitrary Haskell code

module Issue2524 where

open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.String

{-# FOREIGN GHC import qualified Data.Text #-}

postulate
  NativeIO     : Set → Set
  nativeReturn : {A : Set} → A → NativeIO A
  _native>>=_  : {A B : Set} → NativeIO A → (A → NativeIO B) → NativeIO B


{-# BUILTIN IO NativeIO #-}
{-# COMPILE GHC NativeIO = type IO #-}
{-# COMPILE GHC nativeReturn = (\_ -> return :: a -> IO a) #-}
{-# COMPILE GHC _native>>=_ = (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}
{-# COMPILE JS nativeReturn =
    function(u0) { return function(u1) { return function(x) { return function(cb) { cb(x); }; }; }; } #-}
{-# COMPILE JS _native>>=_ =
  function(u0) { return function(u1) { return function(u2) { return function(u3) {
    return function(x) { return function(y) { return function(cb) {
      x(function (xx) { y(xx)(cb); });
  }; }; };
  }; }; }; }
#-}

postulate
  nativePutStrLn  : String → NativeIO ⊤
  primShowNat     : Nat → String

{-# COMPILE GHC nativePutStrLn = (\ s -> putStrLn (Data.Text.unpack s)) #-}
{-# COMPILE GHC primShowNat = Data.Text.pack . show #-}
{-# COMPILE JS nativePutStrLn = function (x) { return function(cb) { process.stdout.write(x + '\n'); cb(0); }; } #-}
{-# COMPILE JS primShowNat = agdaRTS.primShowInteger #-}

abstract
  record Pointer : Set where
    constructor mkPointer
    field thePointer : Nat
          otherInfo  : Nat

  newPointer : Pointer
  newPointer = mkPointer 5 17

  showPointer : Pointer → String
  showPointer p = primShowNat (Pointer.thePointer p)

{-# COMPILE GHC Pointer = type Integer #-}
{-# COMPILE GHC newPointer = 5 #-}
{-# COMPILE GHC showPointer = Data.Text.pack . show #-}
{-# COMPILE JS newPointer = 5 #-}
{-# COMPILE JS showPointer = function(x) { return x; } #-}

main : NativeIO ⊤
main = nativePutStrLn (showPointer newPointer)
