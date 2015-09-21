{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.Erase (eraseTerms) where

import Control.Applicative
import Control.Monad

import Agda.Syntax.Common
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Position
import Agda.Syntax.Treeless
import Agda.Syntax.Literal

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad as I
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Telescope

import Agda.Compiler.Treeless.Subst

import Agda.Utils.Maybe
import Agda.Utils.Impossible

#include "undefined.h"

eraseTerms :: TTerm -> TCM TTerm
eraseTerms = erase
  where
    erase t = case t of

      TApp (TCon c) vs -> do
        rs <- getArgumentRelevance c
        when (length rs < length vs) __IMPOSSIBLE__
        TApp (TCon c) <$> zipWithM eraseRel rs vs

      TApp (TDef f) vs -> do
        rs <- getArgumentRelevance f
        TApp (TDef f) <$> zipWithM eraseRel (rs ++ repeat Relevant) vs

      TVar{}         -> pure t
      TDef{}         -> pure t
      TPrim{}        -> pure t
      TLit{}         -> pure t
      TCon{}         -> pure t
      TApp f es      -> TApp <$> erase f <*> mapM erase es
      TLam b         -> TLam <$> erase b
      TLet e b       -> TLet <$> erase e <*> erase b
      TCase x t d bs -> TCase x t <$> erase d <*> mapM eraseAlt bs

      TPi a b        -> pure TErased
      TUnit          -> pure t
      TSort          -> pure t
      TErased        -> pure t
      TError{}       -> pure t

    eraseRel Relevant   t = erase t
    eraseRel NonStrict  _ = pure TErased
    eraseRel Irrelevant _ = pure TErased
    eraseRel Forced{}   _ = pure TErased
    eraseRel UnusedArg  _ = pure TErased

    eraseAlt a = case a of
      TALit l b   -> TALit l   <$> erase b
      TACon c a b -> TACon c a <$> erase b
      TAPlus k b  -> TAPlus k  <$> erase b

getArgumentRelevance :: QName -> TCM [Relevance]
getArgumentRelevance q = do
  -- TODO: memoize this work!
  def <- getConstInfo q
  TelV tel _ <- telView $ defType def
  let d = case I.theDef def of
        Function{ funProjection = Just Projection{ projIndex = i } } -> i - 1
        Constructor{ conPars = n } -> n
        _                          -> 0
  let rs = map getRelevance $ drop d $ telToList tel
  reportSLn "treeless.opt.erase.rel" 50 $ "arg relevance for " ++ show q ++ ": " ++ show rs
  return rs
