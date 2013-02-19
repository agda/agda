-- | Find the places where the builtin static is used and do some normalisation
--   there.

{-# LANGUAGE CPP #-}

module Agda.Compiler.Epic.Static where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans

import qualified Data.Map as M

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Sharing
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty

import Agda.Utils.Monad
import qualified Agda.Utils.HashMap as HM

import Agda.Compiler.Epic.CompileState

#include "../../undefined.h"
import Agda.Utils.Impossible

normaliseStatic :: CompiledClauses -> Compile TCM CompiledClauses
normaliseStatic = evaluateCC

evaluateCC :: CompiledClauses -> Compile TCM CompiledClauses
evaluateCC ccs = case ccs of
    Case n brs -> do
        cbrs <- forM (M.toList $ conBranches brs) $ \(c, WithArity n cc) -> (,) c <$> (WithArity n <$> evaluateCC cc)
        lbrs <- forM (M.toList $ litBranches brs) $ \(l, cc) -> (,) l <$> evaluateCC cc
        cab <- case catchAllBranch brs of
            Nothing -> return Nothing
            Just cc -> Just <$> evaluateCC cc
        return $ Case n Branches
            { conBranches    = M.fromList cbrs
            , litBranches    = M.fromList lbrs
            , catchAllBranch = cab
            }
    Done n t   -> Done n <$> evaluateTerm t
    Fail       -> return Fail

etaExpand :: Term -> Compile TCM Term
etaExpand def@(Def n ts) = do
    defs <- lift (gets (sigDefinitions . stImports))
    let f   = maybe __IMPOSSIBLE__ theDef (HM.lookup n defs)
        len = length . clausePats . head .  funClauses $ f
        toEta :: Num a => a
        toEta = fromIntegral $ len - length ts
        term  = raise toEta def `apply` [ defaultArg $ Var i [] | i <- [toEta - 1, toEta - 2 .. 0]]
    return $ foldr (\ v t -> Lam defaultArgInfo (Abs v t)) term $ replicate toEta "staticVar"
etaExpand x = return x

evaluateTerm :: Term -> Compile TCM Term
evaluateTerm term = case term of
    Var x as     -> Var x <$>  evaluateTerms as
    Lam h ab     -> do
      ab' <- evaluateTerm (unAbs ab)
      return $ Lam h $ Abs (absName ab) ab'
    Lit l        -> return $ Lit l
    Def n ts -> do
        ifM (not <$> isStatic n)
            (Def n <$> evaluateTerms ts) $ do
                feta <- return term -- etaExpand term
                f <- lift $ normalise feta
                lift $ reportSDoc "epic.static" 10 $ vcat
                  [ text "STATIC pragma fired"
                  , nest 2 $ vcat
                    [ text "before :" <+> prettyTCM term
                    , text "after  :" <+> prettyTCM f
                    ]
                  ]
                return f
    Con c args   -> Con c <$> evaluateTerms args
    Pi  arg abs  -> return $ Pi  arg abs
    Sort s       -> return $ Sort s
    MetaV i args -> return $ MetaV i args
    Level l      -> return $ Level l
    DontCare i   -> return $ DontCare i
    Shared{}     -> updateSharedTermT evaluateTerm term
  where
    evaluateTerms :: Args -> Compile TCM Args
    evaluateTerms as = forM as $ \x -> do
      y <- evaluateTerm (unArg x)
      return x { unArg = y }

    isStatic :: QName -> Compile TCM Bool
    isStatic q = do
      defs <- lift (gets (sigDefinitions . stImports))
      return $ case fmap theDef $ HM.lookup q defs of
          Nothing -> False
          Just (f@Function{}) -> funStatic f
          Just _              -> False
