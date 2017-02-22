-- Andreas, 2016-10-11, AIM XXIV
-- COMPILE GHC pragma accidentially also accepted for abstract definitions

open import Common.String

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () (()) #-}

postulate
  IO : Set → Set
  doNothing : IO Unit

{-# COMPILE GHC IO = type IO #-}
{-# BUILTIN IO IO #-}
{-# COMPILE GHC doNothing = return () #-}

{-# FOREIGN GHC import qualified Data.Text.IO #-}

abstract
  putStrLn : String → IO Unit
  putStrLn _ = doNothing

{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}

main = putStrLn "Hello, world!"

-- WAS: compiler produced ill-formed Haskell-code
-- NOW: Error on COMPILE GHC pragma
