module Issue561.Core where

postulate Char : Set

{-# BUILTIN CHAR Char #-}

open import Agda.Builtin.IO public

postulate
  return  : ∀ {a} {A : Set a} → A → IO A

{-# COMPILE GHC return = \_ _ -> return #-}
{-# COMPILE JS return =
    function(u0) { return function(u1) { return function(x) { return function(cb) { cb(x); }; }; }; } #-}
