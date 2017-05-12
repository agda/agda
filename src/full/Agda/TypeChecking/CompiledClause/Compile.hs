{-# LANGUAGE CPP           #-}

module Agda.TypeChecking.CompiledClause.Compile where

import Prelude hiding (null)

import Control.Monad

import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import Data.List (nubBy)
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
  -- Construct clauses with pattern variables bound in left-to-right order.
  -- Discard de Bruijn indices in patterns.
  cs <- normaliseProjP cs
  let unBruijn cs = [ Cl (map (fmap (fmap dbPatVarName . namedThing)) $ namedClausePats c)
                         (compiledClauseBody c) | c <- cs ]
  shared <- sharedFun
  case mt of
    Nothing -> return $ compile shared $ unBruijn cs
    Just (q, t)  -> do
      splitTree <- coverageCheck q t cs

      -- The coverage checker might have added some clauses (#2288)!
      cs <- normaliseProjP =<< defClauses <$> getConstInfo q
      let cls = unBruijn cs

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
  { clPats :: [Arg Pattern]
      -- ^ Pattern variables are considered in left-to-right order.
  , clBody :: Maybe Term
  } deriving (Show)

instance Pretty Cl where
  pretty (Cl ps b) = P.prettyList ps P.<+> P.text "->" P.<+> maybe (P.text "_|_") pretty b

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
  Nothing -> case clBody c of
    -- It's possible to get more than one clause here due to
    -- catch-all expansion.
    Just t  -> Done (map (fmap name) $ clPats c) (shared t)
    Nothing -> Fail
  where
    -- If there are more than one clauses, take the first one.
    c = headWithDefault __IMPOSSIBLE__ cs
    name (VarP x) = x
    name (DotP _) = underscore
    name AbsurdP{} = absurdPatternName
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
properSplit AbsurdP{} = Nothing -- for purposes of compilation
properSplit DotP{}  = Nothing

-- | Is this a variable pattern?
--
--   Maintain invariant: @isVar = isNothing . properSplit@!
isVar :: Pattern' a -> Bool
isVar VarP{}  = True
isVar DotP{}  = True
isVar AbsurdP{} = True
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
  ProjP _ d   -> projCase d $ Cl (ps0 ++ ps1) b
  ConP c _ qs -> conCase (conName c) $ WithArity (length qs) $
                   Cl (ps0 ++ map (fmap namedThing) qs ++ ps1) b
  LitP l      -> litCase l $ Cl (ps0 ++ ps1) b
  VarP{}      -> fallback
  DotP{}      -> fallback
  AbsurdP{}   -> fallback
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
--
-- Example from issue #2168:
-- @
--   f x     false = a
--   f false       = \ _ -> b
--   f x     true  = c
-- @
-- case tree:
-- @
--   f x y = case y of
--     true  -> case x of
--       true  -> c
--       false -> b
--     false -> a
-- @
expandCatchAlls :: Bool -> Int -> Cls -> Cls
expandCatchAlls single n cs =
  -- Andreas, 2013-03-22
  -- if there is a single case (such as for record splits)
  -- we force expansion
  if single then doExpand =<< cs else
  case cs of
  _                | all (isCatchAllNth . clPats) cs -> cs
  c@(Cl ps b) : cs | not (isCatchAllNth ps) -> c : expandCatchAlls False n cs
                   | otherwise -> map (expand c) expansions ++ c : expandCatchAlls False n cs
  _ -> __IMPOSSIBLE__
  where
    -- In case there is only one branch in the split tree, we expand all
    -- catch-alls for this position
    -- The @expansions@ are collected from all the clauses @cs@ then.
    -- Note: @expansions@ could be empty, so we keep the orignal clause.
    doExpand c@(Cl ps _)
      | exCatchAllNth ps = map (expand c) expansions ++ [c]
      | otherwise = [c]

    -- True if nth pattern is variable or there are less than n patterns.
    isCatchAllNth ps = all (isVar . unArg) $ take 1 $ drop n ps

    -- True if nth pattern exists and is variable.
    exCatchAllNth ps = any (isVar . unArg) $ take 1 $ drop n ps

    classify (LitP l)     = Left l
    classify (ConP c _ _) = Right c
    classify _            = __IMPOSSIBLE__

    -- All non-catch-all patterns following this one (at position n).
    -- These are the cases the wildcard needs to be expanded into.
    expansions = nubBy ((==) `on` (classify . unArg . snd))
               . mapMaybe (notVarNth . clPats)
               $ cs
    notVarNth
      :: [Arg Pattern]
      -> Maybe ([Arg Pattern]  -- First @n@ patterns.
               , Arg Pattern)  -- @n+1@st pattern, not a variable
    notVarNth ps = do
      let (ps1, ps2) = splitAt n ps
      p <- headMaybe ps2
      guard $ not $ isVar $ unArg p
      return (ps1, p)

    expand cl (qs, q) =
      case unArg q of
        ConP c mt qs' -> Cl (ps0 ++ [q $> ConP c mt conPArgs] ++ ps1)
                            (substBody n' m (Con c ci conArgs) b)
          where
            ci       = fromConPatternInfo mt
            m        = length qs'
            -- replace all direct subpatterns of q by _
            conPArgs = map (fmap ($> VarP "_")) qs'
            conArgs  = zipWith (\ q' i -> q' $> var i) qs' $ downFrom m
        LitP l -> Cl (ps0 ++ [q $> LitP l] ++ ps1) (substBody n' 0 (Lit l) b)
        _ -> __IMPOSSIBLE__
      where
        -- Andreas, 2016-09-19 issue #2168
        -- Due to varying function arity, some clauses might be eta-contracted.
        -- Thus, we eta-expand them.
        Cl ps b = ensureNPatterns (n + 1) (map getArgInfo $ qs ++ [q]) cl
        -- The following pattern match cannot fail (by construction of @ps@).
        (ps0, _:ps1) = splitAt n ps

        n' = countVars ps1
        countVars = sum . map (count . unArg)
        count VarP{}        = 1
        count (ConP _ _ ps) = countVars $ map (fmap namedThing) ps
        count DotP{}        = 1   -- dot patterns are treated as variables in the clauses
        count (AbsurdP p)   = count p
        count _             = 0

-- | Make sure (by eta-expansion) that clause has arity at least @n@
--   where @n@ is also the length of the provided list.
ensureNPatterns :: Int -> [ArgInfo] -> Cl -> Cl
ensureNPatterns n ais0 cl@(Cl ps b)
  | m <= 0    = cl
  | otherwise = Cl (ps ++ ps') (raise m b `apply` args)
  where
  k    = length ps
  ais  = drop k ais0
  -- m = Number of arguments to add
  m    = n - k
  ps'  = for ais $ \ ai -> Arg ai $ VarP "_"
  args = zipWith (\ i ai -> Arg ai $ var i) (downFrom m) ais

substBody :: (Subst t a) => Int -> Int -> t -> a -> a
substBody n m v = applySubst $ liftS n $ v :# raiseS m
