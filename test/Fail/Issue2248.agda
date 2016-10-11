-- Andreas, 2016-10-11, AIM XXIV
-- COMPILED pragma accidentially also accepted for abstract definitions

open import Common.String

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}

postulate
  IO : Set → Set
  doNothing : IO Unit

{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}
{-# COMPILED doNothing (return ()) #-}

{-# IMPORT Data.Text.IO #-}

abstract
  putStrLn : String → IO Unit
  putStrLn _ = doNothing

{-# COMPILED putStrLn Data.Text.IO.putStrLn #-}

main = putStrLn "Hello, world!"

-- WAS: compiler produced ill-formed Haskell-code
-- NOW: Error on COMPILED pragma
