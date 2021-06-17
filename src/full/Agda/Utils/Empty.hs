-- | An empty type with some useful instances.
module Agda.Utils.Empty where

import Control.Exception (evaluate)

import Data.Data (Data)

import Agda.Utils.Impossible


data Empty
deriving instance Data Empty

instance Eq Empty where
  _ == _ = True

instance Ord Empty where
  compare _ _ = EQ

instance Show Empty where
  showsPrec p _ = showParen (p > 9) $ showString "error \"Agda.Utils.Empty.Empty\""

absurd :: Empty -> a
absurd e = seq e __IMPOSSIBLE__


-- | @toImpossible e@ extracts the @Impossible@ value raised via
--   @__IMPOSSIBLE__@ to create the element @e@ of type @Empty@.
--   It proceeds by evaluating @e@ to weak head normal form and
--   catching the exception.
--   We are forced to wrap things in a @Maybe@ because of
--   @catchImpossible@'s type.

toImpossible :: Empty -> IO Impossible
toImpossible e = do
  s <- catchImpossible (Nothing <$ evaluate e) (return . Just)
  case s of
    Just i  -> return i
    Nothing -> absurd e -- this should never happen
