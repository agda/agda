module FFI where

postulate
  IO : Set -> Set

{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}

postulate
  return : {A : Set} -> A -> IO A
  _>>=_  : {A B : Set} -> IO A -> (A -> IO B) -> IO B

{-# COMPILED return (\_ -> return :: a -> IO a) #-}
{-# COMPILED _>>=_  (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () nothing #-}

main : IO Unit
main = return unit
