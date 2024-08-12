{-# OPTIONS --no-main #-}

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

{-# COMPILE GHC List = data Non (Sense) #-} -- should result in warning when compiling

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

{-# COMPILE GHC Maybe = data Non (Sense) #-} -- should result in warning when compiling

{-# BUILTIN MAYBE   Maybe   #-}
-- {-# BUILTIN NOTHING nothing #-}
-- {-# BUILTIN JUST    just    #-}

-- Andreas, 2024-08-12
-- Invalid names submitted to COMPILE pragma

{-# COMPILE GHC Set₁ #-} -- name with suffix

data D : Set where
  c : D

record E : Set₁ where
  constructor c
  field f : Set

record R : Set₁ where
  field f : Set

open E
open R

{-# COMPILE GHC c #-}  -- ambiguous name
{-# COMPILE GHC f #-}  -- ambiguous name

pattern p = nothing

{-# COMPILE GHC p #-}  -- pattern synonym

module M (A : Set) where

  {-# COMPILE GHC A #-}  -- variable
