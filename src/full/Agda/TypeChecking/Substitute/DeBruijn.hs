{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Substitute.DeBruijn where

import Agda.Syntax.Common
import Agda.Syntax.Internal

-- | Things we can substitute for a variable.
--   Needs to be able to represent variables, e.g. for substituting under binders.
class DeBruijn a where

  -- | Produce a variable without name suggestion.
  deBruijnVar  :: Int -> a
  deBruijnVar = debruijnNamedVar underscore

  -- | Produce a variable with name suggestion.
  debruijnNamedVar :: String -> Int -> a
  debruijnNamedVar _ = deBruijnVar

  -- | Are we dealing with a variable?
  --   If yes, what is its index?
  deBruijnView :: a -> Maybe Int

-- | We can substitute @Term@s for variables.
instance DeBruijn Term where
  deBruijnVar = var
  deBruijnView u =
    case u of
      Var i [] -> Just i
      Level l -> deBruijnView l
      _ -> Nothing

instance DeBruijn PlusLevel where
  deBruijnVar = Plus 0 . deBruijnVar
  deBruijnView l =
    case l of
      Plus 0 a -> deBruijnView a
      _ -> Nothing

instance DeBruijn Level where
  deBruijnVar i = Max 0 [deBruijnVar i]
  deBruijnView l =
    case l of
      Max 0 [p] -> deBruijnView p
      _ -> Nothing

instance DeBruijn DBPatVar where
  debruijnNamedVar = DBPatVar
  deBruijnView = Just . dbPatVarIndex


instance DeBruijn a => DeBruijn (Named_ a) where
  debruijnNamedVar nm i = unnamed $ debruijnNamedVar nm i
  deBruijnView = deBruijnView . namedThing
