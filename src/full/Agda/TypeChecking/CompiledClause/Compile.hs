{-# LANGUAGE CPP           #-}

module Agda.TypeChecking.CompiledClause.Compile where

import Prelude hiding (null)

import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import Data.List (genericReplicate, nubBy, findIndex)
import Data.Function

import Debug.Trace

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Monad
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty (prettyTCM, nest, sep, text)

import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.List
import Agda.Utils.Pretty (Pretty(..), prettyShow)
import qualified Agda.Utils.Pretty as P

#include "undefined.h"
import Agda.Utils.Impossible

-- | Process function clauses into case tree.
--   This involves:
--   1. Coverage checking, generating a split tree.
--   2. Translation of lhs record patterns into rhs uses of projection.
--      Update the split tree.
--   3. Generating a case tree from the split tree.
--   Phases 1. and 2. are skipped if @Nothing@.
compileClauses ::
  Maybe (QName, Type) -- ^ Translate record patterns and coverage check with given type?
  -> [Clause] -> TCM CompiledClauses
compileClauses mt cs = do
  let cls = [ Cl (clausePats c) (clauseBody c) | c <- cs ]
  shared <- sharedFun
  case mt of
    Nothing -> return $ compile shared cls
    Just (q, t)  -> do
      splitTree <- coverageCheck q t cs

      reportSDoc "tc.cc" 30 $ sep $ do
        (text "clauses patterns  before compilation") : do
          map (prettyTCM . map unArg . clPats) cls
      reportSDoc "tc.cc" 50 $ do
        sep [ text "clauses before compilation"
            , (nest 2 . text . show) cs
            ]
      let cc = compileWithSplitTree shared splitTree cls
      reportSDoc "tc.cc" 12 $ sep
        [ text "compiled clauses (still containing record splits)"
        , nest 2 $ text (show cc)
        ]
      cc <- translateCompiledClauses cc
      return cc

-- | Stripped-down version of 'Agda.Syntax.Internal.Clause'
--   used in clause compiler.
data Cl = Cl
  { clPats :: [Arg DeBruijnPattern]
  , clBody :: ClauseBody
  } deriving (Show)

instance Pretty Cl where
  pretty (Cl ps b) = P.prettyList ps P.<+> P.text "->" P.<+> pretty b

type Cls = [Cl]

compileWithSplitTree :: (Term -> Term) -> SplitTree -> Cls -> CompiledClauses
compileWithSplitTree shared t cs = case t of
  SplitAt i ts -> Case i $ compiles ts $ splitOn (length ts == 1) (unArg i) cs
        -- if there is just one case, we force expansion of catch-alls
        -- this is needed to generate a sound tree on which we can
        -- collapse record pattern splits
  SplittingDone n -> compile shared cs
    -- after end of split tree, continue with left-to-right strategy

  where
    compiles :: SplitTrees -> Case Cls -> Case CompiledClauses
    compiles ts br@Branches{ projPatterns = cop
                           , conBranches = cons
                           , litBranches = lits
                           , catchAllBranch = catchAll }
      = Branches
          { projPatterns   = cop
          , conBranches    = updCons cons
          , litBranches    = compile shared <$> lits
          , catchAllBranch = compile shared <$> catchAll
          }
      where
        updCons = Map.mapWithKey $ \ c cl ->
         caseMaybe (lookup c ts) (compile shared) (compileWithSplitTree shared) <$> cl
         -- When the split tree is finished, we continue with @compile@.

compile :: (Term -> Term) -> Cls -> CompiledClauses
compile shared cs = case nextSplit cs of
  Just (isRecP, n)-> Case n $ fmap (compile shared) $ splitOn isRecP (unArg n) cs
  Nothing -> case map (getBody . clBody) cs of
    -- It's possible to get more than one clause here due to
    -- catch-all expansion.
    Just t : _  -> Done (map (fmap name) $ clPats $ head cs) (shared t)
    Nothing : _ -> Fail
    []          -> __IMPOSSIBLE__
  where
    name (VarP x) = dbPatVarName x
    name (DotP _) = underscore
    name ConP{}  = __IMPOSSIBLE__
    name LitP{}  = __IMPOSSIBLE__
    name ProjP{} = __IMPOSSIBLE__

-- | Get the index of the next argument we need to split on.
--   This the number of the first pattern that does a match in the first clause.
nextSplit :: Cls -> Maybe (Bool, Arg Int)
nextSplit []            = __IMPOSSIBLE__
nextSplit (Cl ps _ : _) = headMaybe $ catMaybes $
  zipWith (\ (Arg ai p) n -> (, Arg ai n) <$> properSplit p) ps [0..]

-- | Is is not a variable pattern?
--   And if yes, is it a record pattern?
properSplit :: Pattern' a -> Maybe Bool
properSplit (ConP _ cpi _) = Just $ isJust $ conPRecord cpi
properSplit LitP{}  = Just False
properSplit ProjP{} = Just False
properSplit VarP{}  = Nothing
properSplit DotP{}  = Nothing

-- | Is this a variable pattern?
--
--   Maintain invariant: @isVar = isNothing . properSplit@!
isVar :: Pattern' a -> Bool
isVar VarP{}  = True
isVar DotP{}  = True
isVar ConP{}  = False
isVar LitP{}  = False
isVar ProjP{} = False

-- | @splitOn single n cs@ will force expansion of catch-alls
--   if @single@.
splitOn :: Bool -> Int -> Cls -> Case Cls
splitOn single n cs = mconcat $ map (fmap (:[]) . splitC n) $
  -- (\ cs -> trace ("splitting on " ++ show n ++ " after expandCatchAlls " ++ show single ++ ": " ++ prettyShow (P.prettyList cs)) cs) $
    expandCatchAlls single n cs

splitC :: Int -> Cl -> Case Cl
splitC n (Cl ps b) = caseMaybe mp fallback $ \case
  ProjP d     -> projCase d $ Cl (ps0 ++ ps1) b
  ConP c _ qs -> conCase (conName c) $ WithArity (length qs) $
                   Cl (ps0 ++ map (fmap namedThing) qs ++ ps1) b
  LitP l      -> litCase l $ Cl (ps0 ++ ps1) b
  VarP{}      -> fallback
  DotP{}      -> fallback
  where
    (ps0, rest) = splitAt n ps
    mp          = unArg <$> headMaybe rest
    ps1         = drop 1 rest
    fallback    = catchAll $ Cl ps b

-- | Expand catch-alls that appear before actual matches.
--
-- Example:
--
-- @
--    true  y
--    x     false
--    false y
-- @
--
-- will expand the catch-all @x@ to @false@.
--
-- Catch-alls need also to be expanded if
-- they come before/after a record pattern, otherwise we get into
-- trouble when we want to eliminate splits on records later.
--
-- Another example (see Issue 1650):
-- @
--   f (x, (y, z)) true  = a
--   f _           false = b
-- @
-- Split tree:
-- @
--   0 (first argument of f)
--    \- 1 (second component of the pair)
--        \- 3 (last argument of f)
--            \-- true  -> a
--             \- false -> b
-- @
-- We would like to get the following case tree:
-- @
--   case 0 of
--   _,_ -> case 1 of
--          _,_ -> case 3 of true  -> a; false -> b
--          _   -> case 3 of true  -> a; false -> b
--   _          -> case 3 of true  -> a; false -> b
-- @
expandCatchAlls :: Bool -> Int -> Cls -> Cls
expandCatchAlls single n cs =
  -- Andreas, 2013-03-22
  -- if there is a single case (such as for record splits)
  -- we force expansion
  if single then doExpand =<< cs else
  case cs of
  _            | all (isCatchAllNth . clPats) cs -> cs
  Cl ps b : cs | not (isCatchAllNth ps) -> Cl ps b : expandCatchAlls False n cs
               | otherwise -> map (expand ps b) expansions ++ Cl ps b : expandCatchAlls False n cs
  _ -> __IMPOSSIBLE__
  where
    -- In case there is only one branch in the split tree, we expand all
    -- catch-alls for this position
    -- The @expansions@ are collected from all the clauses @cs@ then.
    -- Note: @expansions@ could be empty, so we keep the orignal clause.
    doExpand c@(Cl ps b)
      | isVar $ unArg $ nth ps = map (expand ps b) expansions ++ [c]
      | otherwise              = [c]

    -- True if nth pattern is variable or there are less than n patterns.
    isCatchAllNth ps = all (isVar . unArg) $ take 1 $ drop n ps

    nth qs = headWithDefault __IMPOSSIBLE__ $ drop n qs

    classify (LitP l)     = Left l
    classify (ConP c _ _) = Right c
    classify _            = __IMPOSSIBLE__

    -- All non-catch-all patterns following this one (at position n).
    -- These are the cases the wildcard needs to be expanded into.
    expansions = nubBy ((==) `on` (classify . unArg))
               . filter (not . isVar . unArg)
               . map (nth . clPats)
               $ cs

    expand ps b q =
      case unArg q of
        ConP c mt qs' -> Cl (ps0 ++ [q $> ConP c mt conPArgs] ++ ps1)
                            (substBody n' m (Con c conArgs) b)
          where
            m        = length qs'
            -- replace all direct subpatterns of q by _
            conPArgs = map (fmap ($> debruijnNamedVar "_" 0)) qs'
            conArgs  = zipWith (\ q n -> q $> var n) qs' $ downFrom m
        LitP l -> Cl (ps0 ++ [q $> LitP l] ++ ps1) (substBody n' 0 (Lit l) b)
        _ -> __IMPOSSIBLE__
      where
        (ps0, rest) = splitAt n ps
        ps1         = maybe __IMPOSSIBLE__ snd $ uncons rest

        n' = countVars ps0
        countVars = sum . map (count . unArg)
        count VarP{}        = 1
        count (ConP _ _ ps) = countVars $ map (fmap namedThing) ps
        count DotP{}        = 1   -- dot patterns are treated as variables in the clauses
        count _             = 0

substBody :: Int -> Int -> Term -> ClauseBody -> ClauseBody
substBody _ _ _ NoBody = NoBody
substBody 0 m v b = case b of
  Bind   b -> foldr (.) id (replicate m (Bind . Abs underscore)) $ subst 0 v (absBody $ raise m b)
  _        -> __IMPOSSIBLE__
substBody n m v b = case b of
  Bind b   -> Bind $ fmap (substBody (n - 1) m v) b
  _        -> __IMPOSSIBLE__
