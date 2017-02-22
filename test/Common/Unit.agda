module Common.Unit where

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () (()) #-}
{-# COMPILE UHC Unit = data __UNIT__ (__UNIT__) #-}
