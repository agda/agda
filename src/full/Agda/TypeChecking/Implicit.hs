{-# LANGUAGE CPP #-}

{-| Functions for inserting implicit arguments at the right places.
-}
module Agda.TypeChecking.Implicit where

import Agda.Syntax.Common

#include "../undefined.h"
import Agda.Utils.Impossible

data ImplicitInsertion
      = ImpInsert Int	  -- ^ this many implicits have to be inserted
      | BadImplicits	  -- ^ hidden argument where there should have been a non-hidden arg
      | NoSuchName String -- ^ bad named argument
      | NoInsertNeeded
  deriving (Show)

impInsert :: Int -> ImplicitInsertion
impInsert 0 = NoInsertNeeded
impInsert n = ImpInsert n

-- | The list should be non-empty.
insertImplicit :: NamedArg e -> [Arg String] -> ImplicitInsertion
insertImplicit _ [] = __IMPOSSIBLE__
insertImplicit a ts | argHiding a == NotHidden = impInsert $ nofHidden ts
  where
    nofHidden :: [Arg a] -> Int
    nofHidden = length . takeWhile ((Hidden ==) . argHiding)
insertImplicit a ts@(t : _) =
  case argHiding t of
    NotHidden -> BadImplicits
    Hidden    -> case nameOf (unArg a) of
      Nothing -> impInsert 0
      Just x  -> find 0 x ts
  where
    find i x (Arg Hidden r y : ts)
      | x == y	  = impInsert i
      | otherwise = find (i + 1) x ts
    find i x (Arg NotHidden _ _ : _) = NoSuchName x
    find i x []			     = NoSuchName x

