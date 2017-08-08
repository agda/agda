module Issue2486 where

open import Common.Prelude
open import Issue2486.Import
open import Issue2486.ImportB
open import Issue2486.HaskellB

f : MyList String → String
f [] = "sdf"
f (x :: _) = x

xs : MyList String
xs = "sdfg" :: []


{-# FOREIGN GHC import qualified MAlonzo.Code.Issue2486.HaskellB #-}

data Test : Set where
  Con : BBool -> Test
{-# COMPILE GHC Test = data MAlonzo.Code.Issue2486.HaskellB.Test ( MAlonzo.Code.Issue2486.HaskellB.Con ) #-}

{-
ff : BBool
ff = BTrue
-}

main : IO Unit
main =
  putStrLn (f xs)
