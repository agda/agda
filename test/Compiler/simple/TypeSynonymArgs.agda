module TypeSynonymArgs where

postulate
  Functor          : (Set → Set) → Set
  Identity         : Set → Set
  Identity-functor : Functor Identity

{-# FOREIGN GHC import Data.Functor.Identity (Identity) #-}

{-# FOREIGN GHC data FunctorDict f = Functor f => FunctorDict    #-}
{-# COMPILE GHC Functor            = type(0) FunctorDict         #-} -- compiles to `type T_Functor_n = Functor`
{-# COMPILE GHC Identity           = type(0) Identity            #-} -- compiles to `type T_Identity_m = Identity`
{-# COMPILE GHC Identity-functor   = FunctorDict                 #-} -- `Identity` used without args (in type), errors when it is defined eta expanded

--------

postulate
  X : Set → Set

{-# FOREIGN GHC type HsSynonym a = a  #-}

-- Equivalent
{-# COMPILE GHC X = type(1) HsSynonym #-}
-- {-# COMPILE GHC X = type HsSynonym #-}

-- Error (HsSynonym not applied to enough arguments)
-- {-# COMPILE GHC X = type(0) HsSynonym #-}

--------

data Y (a : Set) : Set where
  yy : Y a

{-# FOREIGN GHC data Y a = Y #-}
{-# COMPILE GHC Y = data(0) Y (Y) #-}
