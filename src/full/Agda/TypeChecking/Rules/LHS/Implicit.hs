{-# LANGUAGE CPP, PatternGuards #-}

module Agda.TypeChecking.Rules.LHS.Implicit where

import Data.Maybe
import Control.Applicative

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Info
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Translation.InternalToAbstract (reify)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce

import Agda.TypeChecking.Rules.LHS.Problem

import Agda.Utils.Monad

#include "../../../undefined.h"
import Agda.Utils.Impossible

-- | Insert implicit patterns in a problem.
insertImplicitProblem :: Problem -> TCM Problem
insertImplicitProblem (Problem ps qs tel pr) = do
  reportSDoc "tc.lhs.imp" 15 $
    sep [ text "insertImplicits"
	, nest 2 $ brackets $ fsep $ punctuate comma $ map prettyA ps
	, nest 2 $ prettyTCM tel
	]
  ps' <- insertImplicitPatterns ExpandLast ps tel
  return $ Problem ps' qs tel pr

-- | Eta-expand implicit pattern if of record type.
expandImplicitPattern :: Type -> A.NamedArg A.Pattern -> TCM (A.NamedArg A.Pattern)
expandImplicitPattern a p = maybe (return p) return =<< expandImplicitPattern' a p

-- | Try to eta-expand implicit pattern.
expandImplicitPattern' :: Type -> A.NamedArg A.Pattern -> TCM (Maybe (A.NamedArg A.Pattern))
expandImplicitPattern' a p
  | A.ImplicitP{} <- namedArg p, getHiding p /= Instance = do
     -- Eta expand implicit patterns of record type (issue 473),
     -- but not instance arguments since then they won't be found
     -- by the instance search
     res <- isEtaRecordType =<< reduce a
     flip (maybe (return Nothing)) res $ \ (d, _) -> do
       -- Andreas, 2012-06-10: only expand guarded records,
       -- otherwise we might run into an infinite loop
       c  <- getRecordConstructor d
       fs <- getRecordFieldNames d
       qs <- mapM (\i -> do let Arg info e = implicitP <$ i
                            flip Arg e <$> reify info)
                  fs
       let q  = A.ConP (ConPatInfo True $ PatRange noRange) (A.AmbQ [c]) qs
           p' = updateNamedArg (const q) p   -- WAS: ((q <$) <$> p)  -- Andreas, 2013-03-21 forbiddingly cryptic
       return $ Just p'
  | otherwise = return Nothing

implicitP = unnamed $ A.ImplicitP $ PatRange $ noRange

-- | Insert implicit patterns in a list of patterns.
insertImplicitPatterns :: ExpandHidden -> [A.NamedArg A.Pattern] -> Telescope -> TCM [A.NamedArg A.Pattern]
insertImplicitPatterns exh            ps EmptyTel = return ps
insertImplicitPatterns DontExpandLast [] tel      = return []
insertImplicitPatterns exh ps tel@(ExtendTel arg tel') = case ps of
  [] -> do
    i <- insImp dummy tel
    case i of
      Just []   -> __IMPOSSIBLE__
      Just hs	-> return $ implicitPs hs
      Nothing	-> return []
  p : ps -> do
    i <- insImp p tel
    case i of
      Just []	-> __IMPOSSIBLE__
      Just hs	-> insertImplicitPatterns exh (implicitPs hs ++ p : ps) tel
      Nothing   -> continue =<< expandImplicitPattern (unDom arg) p
        where
          continue p = (p :) <$> insertImplicitPatterns exh ps (absBody tel')
  where
    dummy = defaultNamedArg ()

    insImp x tel = case insertImplicit x $ map (argFromDom . fmap fst) $ telToList tel of
      BadImplicits   -> typeError $ WrongHidingInLHS (telePi tel $ sort Prop)
      NoSuchName x   -> typeError $ WrongHidingInLHS (telePi tel $ sort Prop)
      ImpInsert n    -> return $ Just n
      NoInsertNeeded -> return Nothing

    implicitPs [] = []
    implicitPs (h : hs) = (setHiding h $ defaultArg implicitP) : implicitPs hs
