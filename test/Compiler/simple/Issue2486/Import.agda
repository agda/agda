module Issue2486.Import where

open import Issue2486.Haskell

{-# FOREIGN GHC import qualified MAlonzo.Code.Issue2486.Haskell #-}

data MyList (A : Set) : Set where
  [] : MyList A
  _::_ : A → MyList A → MyList A

{-# COMPILE GHC MyList = data MAlonzo.Code.Issue2486.Haskell.MyList ( MAlonzo.Code.Issue2486.Haskell.Nil | MAlonzo.Code.Issue2486.Haskell.Cons ) #-}
