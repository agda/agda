{-# LANGUAGE CPP #-}
-- Author:  Ulf Norell
-- Created: 2013-11-09

{-|
  This module defines an inlining transformation on clauses that's run before
  termination checking. The purpose is to improve termination checking of with
  clauses (issue 59). The transformation inlines generated with-functions
  expanding the clauses of the parent function in such a way that termination
  checking the expanded clauses guarantees termination of the original function,
  while allowing more terminating functions to be accepted. It does in no way
  pretend to preserve the semantics of the original function.

  Roughly, the source program

> f ps with as
> {f ps₁i qsi = bi}

  is represented internally as

> f ps = f-aux xs as      where xs   = vars(ps)
> {f-aux ps₂i qsi = bi}   where ps₁i = ps[ps₂i/xs]

  The inlining transformation turns this into

> {f ps = aj} for aj ∈ as
> {f ps₁i qsi bi}

  The first clauses ensure that we don't forget any recursive calls in @as@.

  The reason this works is that there is a single call site for each
  with-function.
 -}
module Agda.Termination.Inlining (inlineWithClauses, isWithFunction) where

import Control.Applicative
import Control.Monad.State
import Data.Monoid
import Data.Foldable (foldMap)
import Data.Traversable (traverse)
import Data.List as List

import Agda.Syntax.Common hiding (NamedArg)
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.DisplayForm
import Agda.TypeChecking.Telescope
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Size

import Agda.Utils.Impossible
#include "../undefined.h"

inlineWithClauses :: Clause -> TCM [Clause]
inlineWithClauses cl = inTopContext $ addCtxTel (clauseTel cl) $
  case getRHS $ clauseBody cl of
    Just (Def wf els) -> do
      w <- isWithFunction wf
      case w of
        Nothing -> return [cl]
        Just f  -> do
          reportSDoc "term.inline" 20 $ inTopContext $ sep [text "Found with:", nest 2 $ prettyTCM $ QNamed f cl]
          t   <- defType <$> getConstInfo wf
          let args = allArgs els
          cs1 <- withExprClauses cl t args
          cs2 <- inlinedClauses f cl t wf
          let cs = cs1 ++ cs2
          reportSDoc "term.inline" 20 $ inTopContext $ vcat $ text "After inlining" :
                                                              map (nest 2 . prettyTCM . QNamed f) cs
          return cs
    _ -> return [cl]
  where
    allArgs :: Elims -> Args
    allArgs (Apply a : es) = a : allArgs es
    allArgs (Proj{} : _)   = __IMPOSSIBLE__
    allArgs []             = []

    getRHS (Body v) = Just v
    getRHS (Bind b) = getRHS $ unAbs b
    getRHS NoBody   = Nothing

withExprClauses :: Clause -> Type -> Args -> TCM [Clause]
withExprClauses cl t []     = return []
withExprClauses cl t (a:as) =
  case unArg a of
    Var i [] -> rest
    v        ->
      (cl { clauseBody = v <$ clauseBody cl
          , clauseType = Just $ defaultArg dom
          } :) <$> rest
  where
    rest = withExprClauses cl (piApply t [a]) as
    dom  = case unEl t of   -- The type is the generated with-function type so we know it
      Pi a _  -> unDom a    -- doesn't contain anything funny
      _       -> __IMPOSSIBLE__

inlinedClauses :: QName -> Clause -> Type -> QName -> TCM [Clause]
inlinedClauses f cl t wf = do
  wcs <- concat <$> (mapM inlineWithClauses =<< defClauses <$> getConstInfo wf)
  reportSDoc "term.inline" 30 $ inTopContext $
                                vcat $ text "With-clauses to inline" :
                                       map (nest 2 . prettyTCM . QNamed wf) wcs
  mapM (inline f cl t wf) wcs

inline :: QName -> Clause -> Type -> QName -> Clause -> TCM Clause
inline f pcl t wf wcl = inTopContext $ addCtxTel (clauseTel wcl) $ do
  -- The tricky part here is to get the variables to line up properly. The
  -- order of the arguments to the with-function is not the same as the order
  -- of the arguments to the parent function. Fortunately we have already
  -- figured out how to turn an application of the with-function into an
  -- application of the parent function in the display form.
  let vs = clauseArgs wcl
  Just disp <- displayForm wf vs
  (pats, perm) <- dispToPats disp

  -- Now we need to sort out the right hand side. We have
  --    Γ  - clause telescope (same for with-clause and inlined clause)
  --    Δw - variables bound in the patterns of the with clause
  --    Δi - variables bound in the patterns of the inlined clause
  --    Δw ⊢ clauseBody wcl
  -- and we want
  --    Δi ⊢ body
  -- We can use the clause permutations to get there (renaming is bugged and
  -- shouldn't need the reverseP):
  --    applySubst (renaming $ reverseP $ clausePerm wcl) : Term Δw -> Term Γ
  --    applySubst (renamingR perm)                       : Term Γ -> Term Δi
  -- Finally we need to add the right number of Bind's to the body.
  let body = rebindBody (permRange perm) $
             applySubst (renamingR perm) .
             applySubst (renaming $ reverseP $ clausePerm wcl)
              <$> clauseBody wcl
  return wcl { clausePerm      = perm
             , namedClausePats = pats
             , clauseBody      = body
             , clauseType      = Nothing -- TODO: renaming of original clause type
             }
  where
    numVars  = size (clauseTel wcl)

    getBody = getFirst . foldMap (First . Just)
    rebindBody n b = bind n $ maybe NoBody Body $ getBody b
      where
        bind 0 = id
        bind n = Bind . Abs ("h" ++ show n') . bind n'
          where n' = n - 1

    dtermToTerm DWithApp{} = __IMPOSSIBLE__   -- patsToTerms doesn't generate DWithApps
    dtermToTerm (DCon c args) = Con (ConHead c []) $ map (fmap dtermToTerm) args
    dtermToTerm (DDef f args) = Def f $ map (Apply . fmap dtermToTerm) args
    dtermToTerm (DDot v)      = v
    dtermToTerm (DTerm v)     = v

    dispToPats :: DisplayTerm -> TCM ([NamedArg Pattern], Permutation)
    dispToPats (DWithApp (DDef _ vs : ws) zs) = do
      let us = vs ++ map defaultArg ws ++ map (fmap DTerm) zs
      (ps, (j, ren)) <- (`runStateT` (0, [])) $
                        map (fmap unnamed) <$> mapM (traverse dtermToPat) us
      let perm = Perm j (map snd $ List.sort ren)
          qs   = applySubst (renamingR $ compactP perm) ps
                    -- Need to substitute dot patterns in ps.
                    -- In the dot patterns only actual variables counts as
                    -- binding, as opposed to in the body where dot patterns
                    -- are (unused) bindings as well. Compacting the
                    -- permutation accounts for this.
      return (qs, perm)
    dispToPats t = __IMPOSSIBLE__

    bindVar i = do
      (j, is)  <- get
      let i' = numVars - i - 1
      case lookup i' is of
        Nothing -> True  <$ put (j + 1, (i', j) : is)
        Just{}  -> False <$ put (j + 1, is)

    skip = modify $ \(j, is) -> (j + 1, is)

    dtermToPat v =
      case v of
        DWithApp{}       -> __IMPOSSIBLE__   -- I believe
        DCon c vs        -> ConP (ConHead c []) Nothing . map (fmap unnamed)
                              <$> mapM (traverse dtermToPat) vs
        DDef{}           -> DotP (dtermToTerm v) <$ skip
        DDot v           -> DotP v <$ skip
        DTerm (Var i []) ->
          ifM (bindVar i) (VarP . show <$> lift (nameOfBV i))
                          (pure $ DotP (Var i []))
        DTerm (Con c vs) -> ConP c Nothing . map (fmap unnamed) <$> mapM (traverse (dtermToPat . DTerm)) vs
        DTerm v          -> DotP v <$ skip

isWithFunction :: QName -> TCM (Maybe QName)
isWithFunction x = do
  def <- getConstInfo x
  return $ case theDef def of
    Function{ funWith = w } -> w
    _                       -> Nothing

