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

postulate
  toBList : ∀ {A} → MyList A → BList A
  fromBList : ∀ {A} → BList A → MyList A

{-# COMPILE GHC toBList   = \ _ xs -> xs #-}
{-# COMPILE GHC fromBList = \ _ xs -> xs #-}


{-# FOREIGN GHC import qualified MAlonzo.Code.Issue2486.HaskellB as B #-}

data Test : Set where
  Con : BBool → Test
{-# COMPILE GHC Test = data B.Test ( B.Con ) #-}

{-
ff : BBool
ff = BTrue
-}

main : IO Unit
main =
  putStrLn (f (fromBList (toBList xs)))
