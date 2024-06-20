{-# OPTIONS_GHC -Wunused-imports #-}

-- | An empty type with some useful instances.
module Agda.Utils.Empty where

import Control.DeepSeq ( NFData(..) )
import Control.Exception (evaluate)

import Agda.Utils.Impossible
    ( CatchImpossible(catchImpossible), Impossible, __IMPOSSIBLE__ )


data Empty

-- | Values of type 'Empty' are not forced, because 'Empty' is used as
-- a constructor argument in 'Agda.Syntax.Internal.Substitution''.

instance NFData Empty where
  rnf :: Empty -> ()
  rnf _ = ()

instance Eq Empty where
  (==) :: Empty -> Empty -> Bool
  _ == _ = True

instance Ord Empty where
  compare :: Empty -> Empty -> Ordering
  compare _ _ = EQ

instance Show Empty where
  showsPrec :: Int -> Empty -> ShowS
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
