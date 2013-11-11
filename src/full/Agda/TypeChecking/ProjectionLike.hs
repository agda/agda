{-# LANGUAGE CPP, PatternGuards, TypeSynonymInstances, FlexibleInstances #-}
module Agda.TypeChecking.ProjectionLike where

import Control.Monad

import qualified Data.Map as Map

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal as I

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Free (isBinderUsed)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce (reduce)

import Agda.TypeChecking.DropArgs

import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Permutation

#include "../undefined.h"
import Agda.Utils.Impossible

-- | View for a @Def f (Apply a : es)@ where @isProjection f@.
--   Used for projection-like @f@s.
data ProjectionView = ProjectionView
  { projViewProj  :: QName
  , projViewSelf  :: I.Arg Term
  , projViewSpine :: Elims
  }

-- | Semantics of 'ProjectionView'.
unProjView :: ProjectionView -> Term
unProjView (ProjectionView f a es) = Def f (Apply a : es)

-- | Top-level 'ProjectionView' (no reduction).
projView :: Term -> TCM (Maybe ProjectionView)
projView v = do
  case ignoreSharing v of
    Def f (Apply a : es) -> (ProjectionView f a es <$) <$> isProjection f
    _                    -> return Nothing

-- | Reduce away top-level projection like functions.
--   (Also reduces projections, but they should not be there,
--   since Internal is in lambda- and projection-beta-normal form.)
--
reduceProjectionLike :: Term -> TCM Term
reduceProjectionLike v =
  -- Andreas, 2013-11-01 make sure we do not reduce a constructor
  -- because that could be folded back into a literal by reduce.
  maybeM (return v) (\ _ -> onlyReduceProjections $ reduce v) $ projView v
                            -- ordinary reduce, only different for Def's

-- | Turn prefix projection-like function application into postfix ones.
--   This does just one layer, such that the top spine contains
--   the projection-like functions as projections.
--   Used in 'compareElims' in @TypeChecking.Conversion@
--   and in 'Agda.TypeChecking.CheckInternal'.
--
--   No precondition.
--   Preserves constructorForm, since it really does only something
--   applications of projection-like functions.
elimView :: Term -> TCM Term
elimView v = do
  reportSDoc "tc.conv.elim" 30 $ text "elimView of " <+> prettyTCM v
  reportSLn  "tc.conv.elim" 50 $ "v = " ++ show v
  v <- reduceProjectionLike v
  reportSDoc "tc.conv.elim" 40 $
    text "elimView (projections reduced) of " <+> prettyTCM v
  caseMaybeM (projView v) (return v) $ \ (ProjectionView f a es) -> do
        (`applyE` (Proj f : es)) <$> elimView (unArg a)

{- Andreas, 2013-11-01: Use of unLevel no longer necessary, since we do not reduce!
  case ignoreSharing v of
    Def f (Apply (Arg _ rv) : es) -> do
      flip (maybeM (return v)) (isProjection f) $ \ _ -> do
        (`applyE` (Proj f : es)) <$> do elimView =<< unLevel =<< reduce rv
          -- domi 2012-7-24: Add unLevel to handle neutral levels.
          -- The problem is that reduce turns @suc (neutral)@
          -- into @Level (Max [Plus 1 (NeutralLevel neutral)])@
          -- which the below pattern match does not handle.
    _ -> return v
-}

-- | Which @Def@types are eligible for the principle argument
--   of a projection-like function?
eligibleForProjectionLike :: QName -> TCM Bool
eligibleForProjectionLike d = do
  defn <- theDef <$> getConstInfo d
  return $ case defn of
    Datatype{} -> True
    Record{}   -> True
    Axiom{}    -> True
    _          -> False

-- | Turn a definition into a projection if it looks like a projection.
makeProjection :: QName -> TCM ()
makeProjection x = inTopContext $ do
  -- reportSLn "tc.proj.like" 30 $ "Considering " ++ show x ++ " for projection likeness"
  defn <- getConstInfo x
  let t = defType defn
  reportSDoc "tc.proj.like" 20 $ sep
    [ text "Checking for projection likeness "
    , prettyTCM x <+> text " : " <+> prettyTCM t
    ]
  case theDef defn of
    -- Constructor-headed functions can't be projection-like (at the moment). The reason
    -- for this is that invoking constructor-headedness will circumvent the inference of
    -- the dropped arguments.
    -- Nor can abstract definitions be projection-like since they won't reduce
    -- outside the abstract block.
    def@Function{funProjection = Nothing, funClauses = cls, funCompiled = cc0, funInv = NotInjective,
                 funMutual = [], -- Andreas, 2012-09-28: only consider non-mutual funs (or those whose recursion status has not yet been determined)
                 funAbstr = ConcreteDef} -> do
      ps0 <- filterM validProj $ candidateArgs [] t
      reportSLn "tc.proj.like" 30 $ if null ps0 then "  no candidates found"
                                                else "  candidates: " ++ show ps0
      unless (null ps0) $ do
      -- Andreas 2012-09-26: only consider non-recursive functions for proj.like.
      -- Issue 700: problems with recursive funs. in term.checker and reduction
      ifM recursive (reportSLn "tc.proj.like" 30 $ "recursive functions are not considered for projection-likeness") $ do
      ps <- return $ filter (checkOccurs cls . snd) ps0
      when (not (null ps0) && null ps) $
        reportSLn "tc.proj.like" 50 $
          "  occurs check failed\n    clauses = " ++ show cls
      case reverse ps of
        []         -> return ()
        (d, n) : _ -> do
          reportSDoc "tc.proj.like" 10 $ sep
            [ prettyTCM x <+> text " : " <+> prettyTCM t
            , text $ " is projection like in argument " ++ show n ++ " for type " ++ show d
            ]
{-
          reportSLn "tc.proj.like" 10 $
            show (defName defn) ++ " is projection like in argument " ++
            show n ++ " for type " ++ show d
-}
          let cls' = map (dropArgs n) cls
              cc   = dropArgs n cc0
          -- cc <- compileClauses (Just (x, __IMPOSSIBLE__)) cls'
          reportSLn "tc.proj.like" 60 $ "  rewrote clauses to\n    " ++ show cc

          -- Andreas, 2013-10-20 build parameter dropping function
          let ptel = take n $ telToList $ theTel $ telView' t
              -- leading lambdas are to ignore parameter applications
              proj = teleNoAbs ptel $ Def x []
              -- proj = foldr (\ (Dom ai (y, _)) -> Lam ai . NoAbs y) (Def x []) ptel

          let projection = Projection
                { projProper   = Nothing
                , projFromType = d
                , projIndex    = n + 1
                , projDropPars = proj
                }
          let newDef = def
                       { funProjection     = Just projection
                       , funClauses        = cls'
                       , funCompiled       = cc
                       , funInv            = dropArgs n $ funInv def
                       }
          addConstant x $ defn { defPolarity       = drop n $ defPolarity defn
                               , defArgOccurrences = drop n $ defArgOccurrences defn
                               , defDisplay        = []
                               , theDef            = newDef
                               }
    Function{funInv = Inverse{}} ->
      reportSLn "tc.proj.like" 30 $ "  injective functions can't be projections"
    Function{funAbstr = AbstractDef} ->
      reportSLn "tc.proj.like" 30 $ "  abstract functions can't be projections"
    Function{funProjection = Just{}} ->
      reportSLn "tc.proj.like" 30 $ "  already projection like"
    _ -> reportSLn "tc.proj.like" 30 $ "  not a function"
  where
    -- @validProj (d,n)@ checks whether the head @d@ of the type of the
    -- @n@th argument is injective in all args (i.d. being name of data/record/axiom).
    validProj :: (QName, Int) -> TCM Bool
    validProj (_, 0) = return False
    validProj (d, _) = eligibleForProjectionLike d

    recursive = do
      occs <- computeOccurrences x
      let xocc = Map.lookup (ADef x) occs
      case xocc of
        Just (_ : _) -> return True -- recursive occurrence
        _            -> return False

    checkOccurs cls n = all (nonOccur n) cls

    nonOccur n cl =
      and [ take n p == [0..n - 1]
          , onlyMatch n ps  -- projection-like functions are only allowed to match on the eliminatee
                            -- otherwise we may end up projecting from constructor applications, in
                            -- which case we can't reconstruct the dropped parameters
          , checkBody n b ]
      where
        Perm _ p = clausePerm cl
        ps       = namedClausePats cl
        b        = clauseBody cl


    onlyMatch n ps = all (shallowMatch . namedArg) (take 1 ps1) &&
                     noMatches (ps0 ++ drop 1 ps1)
      where
        (ps0, ps1) = splitAt n ps
        shallowMatch (ConP _ _ ps) = noMatches ps
        shallowMatch _             = True
        noMatches = all (noMatch . namedArg)
        noMatch ConP{} = False
        noMatch LitP{} = False
        noMatch ProjP{}= False
        noMatch VarP{} = True
        noMatch DotP{} = True

    checkBody 0 _          = True
    checkBody _ NoBody     = False    -- absurd clauses are not permitted
    checkBody n (Bind b)   = not (isBinderUsed b) && checkBody (n - 1) (unAbs b)
    checkBody _ Body{}     = __IMPOSSIBLE__

    -- @candidateArgs [var 0,...,var(n-1)] t@ adds @(n,d)@ to the output,
    -- if @t@ is a function-type with domain @t 0 .. (n-1)@
    -- (the domain of @t@ is the type of the arg @n@).
    --
    -- This means that from the type of arg @n@ all previous arguments
    -- can be computed by a simple matching.
    -- (Provided the @d@ is data/record/postulate, checked in @validProj@).
    --
    -- E.g. f : {x : _}(y : _){z : _} -> D x y z -> ...
    -- will return (D,3) as a candidate (amongst maybe others).
    --
    candidateArgs :: [Term] -> Type -> [(QName,Int)]
    candidateArgs vs t =
      case ignoreSharing $ unEl t of
        Pi a b
          | Def d es <- ignoreSharing $ unEl $ unDom a,
            Just us  <- allApplyElims es,
            vs == map unArg us -> (d, length vs) : candidateRec b
          | otherwise          -> candidateRec b
        _                      -> []
      where
        candidateRec NoAbs{}   = []
        candidateRec (Abs x t) = candidateArgs (var (size vs) : vs) t

{-
    candidateArgs :: [Term] -> Term -> [(QName,Int)]
    candidateArgs vs (Shared p) = candidateArgs vs $ derefPtr p
    candidateArgs vs (Pi (Dom info (El _ def)) b)
      | Def d es <- ignoreSharing def,
        Just us <- allApplyElims es,
        vs == map unArg us    = (d, length vs) : candidateRec vs b
    candidateArgs vs (Pi _ b) = candidateRec vs b
    candidateArgs _ _ = []

    candidateRec vs NoAbs{} = []
    candidateRec vs b       = candidateArgs (var (size vs) : vs) (unEl $ absBody b)
-}
