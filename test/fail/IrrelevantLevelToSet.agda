{-# OPTIONS --universe-polymorphism #-}
module IrrelevantLevelToSet where

data Level : Set where
  zero : Level
  suc  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

-- should fail, because Set i /= Set j for i /= j, so i is not irrelevant in Set i
MySet : .(i : Level) -> Set (suc i)
MySet i = Set i
