module Issue2486.ImportB where

open import Issue2486.Haskell

{-# FOREIGN GHC data BBool = BTrue | BFalse #-}
data BBool : Set where
  BTrue BFalse : BBool
{-# COMPILE GHC BBool = data MAlonzo.Code.Issue2486.ImportB.BBool ( MAlonzo.Code.Issue2486.ImportB.BTrue | MAlonzo.Code.Issue2486.ImportB.BFalse ) #-}

