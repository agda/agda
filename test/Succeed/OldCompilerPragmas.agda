
module _ where

data Bool : Set where
  false true : Bool

{-# COMPILED_DATA Bool Bool False True #-}

postulate
  IO : Set → Set
  return : {A : Set} → A → IO A

{-# COMPILED_TYPE IO IO #-}
{-# COMPILED return \ _ -> return #-}
{-# COMPILED_UHC return \ _ x -> UHC.Agda.Builtins.primReturn x #-}
{-# COMPILED_JS return function(u) { return function(x) { return function(cb) { cb(x); }; }; } #-}

{-# IMPORT Data.Maybe #-}

{-# HASKELL printMaybe = putStrLn . Data.Maybe.fromMaybe "" #-}

returnTrue : IO Bool
returnTrue = return true

{-# COMPILED_EXPORT  returnTrue returnTrue #-}
