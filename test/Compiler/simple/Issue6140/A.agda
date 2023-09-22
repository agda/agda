module Issue6140.A where

open import Agda.Builtin.List using (List)

postulate
    Functor : (Set -> Set) -> Set

{-# FOREIGN GHC data AgdaFunctor f = Functor f => AgdaFunctor #-}
{-# COMPILE GHC Functor = type AgdaFunctor #-}

postulate
    List-Functor : Functor List

{-# COMPILE GHC List-Functor = AgdaFunctor #-}
