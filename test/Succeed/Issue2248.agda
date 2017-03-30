-- Andreas, 2016-10-11, AIM XXIV
-- COMPILED pragma accidentially also accepted for abstract definitions
-- Ulf, 2017-02-22: We now allow COMPILE pragmas on functions, and abstract
-- functions should not be an exception. The original problem, however, was
-- that we expected an unused argument-version of the function to be available.
-- This is not the case for COMPILE'd functions. This problem has now been
-- fixed.

open import Common.String

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () (()) #-}

postulate
  IO : Set → Set
  doNothing : IO Unit
  doSomething : String → IO Unit

{-# COMPILE GHC IO = type IO #-}
{-# BUILTIN IO IO #-}
{-# COMPILE GHC doNothing = return () #-}

{-# FOREIGN GHC import qualified Data.Text.IO #-}

abstract
  putStrLn : Unit → String → IO Unit
  putStrLn _ = doSomething

{-# COMPILE GHC putStrLn = \ _ -> Data.Text.IO.putStrLn #-}

main = putStrLn unit "Hello, world!"

-- WAS: compiler produced ill-formed Haskell-code
-- WAS: Error on COMPILE GHC pragma
-- NOW: should succeed
