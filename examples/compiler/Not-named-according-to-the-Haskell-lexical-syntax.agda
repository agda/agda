module Not-named-according-to-the-Haskell-lexical-syntax where

postulate
  IO : Set -> Set

{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}

postulate
  return : {A : Set} -> A -> IO A

{-# COMPILED return (\_ -> return :: a -> IO a) #-}
{-# COMPILED_EPIC return (u1 : Unit, a : Any) -> Any = ioreturn(a) #-}

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}
