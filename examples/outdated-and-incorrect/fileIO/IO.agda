
module IO where

open import Base

postulate
  IO       : Set -> Set
  getLine  : IO String
  putStrLn : String -> IO Unit
  mapM₋    : {A : Set} -> (A -> IO Unit) -> List A -> IO Unit
  bindIO   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
  returnIO : {A : Set} -> A -> IO A

{-# COMPILED putStrLn putStrLn #-}
{-# COMPILED mapM₋ (\_ -> mapM_ :: (a -> IO ()) -> [a] -> IO ()) #-}
  -- we need to throw away the type argument to mapM_
  -- and resolve the overloading explicitly (since Alonzo
  -- output is sprinkled with unsafeCoerce#).
{-# COMPILED bindIO (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}
{-# COMPILED returnIO (\_ -> return :: a -> IO a) #-}
{-# COMPILED getLine getLine #-}
  