module Not-named-according-to-the-Haskell-lexical-syntax where

postulate
  IO : Set -> Set

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

postulate
  return : {A : Set} -> A -> IO A

{-# COMPILE GHC return = \ _ -> return :: a -> IO a #-}

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () (()) #-}
