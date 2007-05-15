{-# OPTIONS -cpp #-}

{-| Functions for inserting implicit arguments at the right places.
-}
module TypeChecking.Implicit where

import Syntax.Common

#include "../undefined.h"

data ImplicitInsertion
      = ImpInsert Int	  -- ^ this many implicits have to be inserted
      | BadImplicits	  -- ^ hidden argument where there should have been a non-hidden arg
      | NoSuchName String -- ^ bad named argument
      | NoInsertNeeded

-- | The list should be non-empty.
insertImplicit :: NamedArg e -> [Arg String] -> ImplicitInsertion
insertImplicit _ []		    = __IMPOSSIBLE__
insertImplicit (Arg NotHidden _) ts = ImpInsert $ nofHidden ts
  where
    nofHidden :: [Arg a] -> Int
    nofHidden = length . takeWhile ((Hidden ==) . argHiding)
insertImplicit (Arg _ e) ts@(t : _) =
  case argHiding t of
    NotHidden -> BadImplicits
    Hidden    -> case nameOf e of
      Nothing -> ImpInsert 0
      Just x  -> find 0 x ts
  where
    find i x (Arg Hidden y : ts)
      | x == y	  = ImpInsert i
      | otherwise = find (i + 1) x ts
    find i x (Arg NotHidden _ : _) = NoSuchName x
    find i x []			   = NoSuchName x

