module SimpleIO where

{-# IMPORT Data.Text.IO #-}

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}

postulate
  String : Set

{-# BUILTIN STRING String #-}

postulate
  IO : Set → Set

{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}

postulate
  putStr putStrLn : String → IO Unit

postulate
  primStringAppend : String -> String -> String

infixr 5 _&_
_&_ = primStringAppend

{-# COMPILED putStr Data.Text.IO.putStr #-}

private
  main : IO Unit
  main = putStr "Hello, World!"
