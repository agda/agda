module Not-named-according-to-the-Haskell-lexical-syntax where

postulate
  IO : Set -> Set

{-# COMPILED_TYPE IO IO #-}

postulate
  return : {A : Set} -> A -> IO A

{-# COMPILED return (\_ -> return :: a -> IO a) #-}

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}
