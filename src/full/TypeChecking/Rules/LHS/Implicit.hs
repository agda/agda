{-# OPTIONS -cpp #-}

module TypeChecking.Rules.LHS.Implicit where

import Control.Applicative

import Syntax.Common
import Syntax.Position
import Syntax.Info
import Syntax.Internal
import qualified Syntax.Abstract as A

import TypeChecking.Monad
import TypeChecking.Implicit
import TypeChecking.Substitute
import TypeChecking.Pretty

import TypeChecking.Rules.LHS.Problem

#include "../../../undefined.h"

-- | Insert implicit patterns in a problem.
insertImplicitProblem :: Problem -> TCM Problem
insertImplicitProblem (Problem ps qs tel) = do
  reportSDoc "tc.lhs.imp" 15 $
    sep [ text "insertImplicits"
	, nest 2 $ brackets $ fsep $ punctuate comma $ map prettyA ps
	, nest 2 $ prettyTCM tel
	]
  ps' <- insertImplicitPatterns ps tel
  return $ Problem ps' qs tel

-- | Insert implicit patterns in a list of patterns.
insertImplicitPatterns :: [NamedArg A.Pattern] -> Telescope -> TCM [NamedArg A.Pattern]
insertImplicitPatterns ps EmptyTel = return ps
insertImplicitPatterns ps tel@(ExtendTel _ tel') = case ps of
  [] -> do
    i <- insImp dummy tel
    case i of
      Just n	-> return $ replicate n implicitP
      Nothing	-> return []
  p : ps -> do
    i <- insImp p tel
    case i of
      Just 0	-> __IMPOSSIBLE__
      Just n	-> insertImplicitPatterns (replicate n implicitP ++ p : ps) tel
      Nothing	-> (p :) <$> insertImplicitPatterns ps (absBody tel')
  where
    dummy = Arg NotHidden $ unnamed ()

    insImp x tel = case insertImplicit x $ map (fmap fst) $ telToList tel of
      BadImplicits   -> typeError $ WrongHidingInLHS (telePi tel $ sort Prop)
      NoSuchName x   -> typeError $ WrongHidingInLHS (telePi tel $ sort Prop)
      ImpInsert n    -> return $ Just n
      NoInsertNeeded -> return Nothing

    implicitP = Arg Hidden . unnamed . A.ImplicitP . PatRange $ noRange

