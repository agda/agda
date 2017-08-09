module Issue2486.ImportB where

open import Issue2486.Haskell

{-# FOREIGN GHC data BBool = BTrue | BFalse #-}
data BBool : Set where
  BTrue BFalse : BBool

{-# COMPILE GHC BBool = data BBool ( BTrue | BFalse ) #-}

postulate BList : Set → Set
{-# FOREIGN GHC import MAlonzo.Code.Issue2486.Haskell (MyList) #-}
{-# COMPILE GHC BList = type MyList #-}
