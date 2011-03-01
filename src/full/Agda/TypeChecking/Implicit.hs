{-# LANGUAGE CPP #-}

{-| Functions for inserting implicit arguments at the right places.
-}
module Agda.TypeChecking.Implicit where

import Agda.Syntax.Common

#include "../undefined.h"
import Agda.Utils.Impossible
import Control.Applicative

data ImplicitInsertion
      = ImpInsert [Hiding]	  -- ^ this many implicits have to be inserted
      | BadImplicits	  -- ^ hidden argument where there should have been a non-hidden arg
      | NoSuchName String -- ^ bad named argument
      | NoInsertNeeded
  deriving (Show)

impInsert :: [Hiding] -> ImplicitInsertion
impInsert [] = NoInsertNeeded
impInsert hs = ImpInsert hs

-- | The list should be non-empty.
insertImplicit :: NamedArg e -> [Arg String] -> ImplicitInsertion
insertImplicit _ [] = __IMPOSSIBLE__
insertImplicit a ts | argHiding a == NotHidden = impInsert $ nofHidden ts
  where
    nofHidden :: [Arg a] -> [Hiding]
    nofHidden = takeWhile (NotHidden /=) . map argHiding
insertImplicit a ts =
  case nameOf (unArg a) of
    Nothing -> maybe BadImplicits impInsert $ upto (argHiding a) $ map argHiding ts
    Just x  -> find [] x (argHiding a) ts
  where
    upto h [] = Nothing
    upto h (NotHidden:_) = Nothing
    upto h (h':_) | h == h' = Just []
    upto h (h':hs) = (h':) <$> upto h hs
    find _ x _ (Arg NotHidden _ _ : _) = NoSuchName x
    find hs x hidingx (Arg hidingy r y : ts)
      | x == y && hidingx == hidingy = impInsert $ reverse hs
      | x == y && hidingx /= hidingy = BadImplicits
      | otherwise = find (hidingy:hs) x hidingx ts
    find i x _ []			     = NoSuchName x
