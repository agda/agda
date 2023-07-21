{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.CompiledClause.Compile where

import Prelude hiding (null)

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Identity

import Data.Maybe
import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Monad
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Free.Precompute
import Agda.TypeChecking.Reduce

import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.List
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Utils.Size
import Agda.Utils.Update

import Agda.Utils.Impossible

data RunRecordPatternTranslation = RunRecordPatternTranslation | DontRunRecordPatternTranslation
  deriving (Eq)

compileClauses' :: RunRecordPatternTranslation -> [Clause] -> Maybe SplitTree -> TCM CompiledClauses
compileClauses' recpat cs mSplitTree = do

  -- Throw away the unreachable clauses (#2723).
  let notUnreachable = (Just True /=) . clauseUnreachable
  cs <- map unBruijn <$> normaliseProjP (filter notUnreachable cs)

  let translate | recpat == RunRecordPatternTranslation = runIdentityT . translateCompiledClauses
                | otherwise                             = return

  translate $ caseMaybe mSplitTree (compile cs) $ \splitTree ->
    compileWithSplitTree splitTree cs

-- | Process function clauses into case tree.
--   This involves:
--   1. Coverage checking, generating a split tree.
--   2. Translation of lhs record patterns into rhs uses of projection.
--      Update the split tree.
--   3. Generating a case tree from the split tree.
--   Phases 1. and 2. are skipped if @Nothing@.
compileClauses ::
  Maybe (QName, Type) -- ^ Translate record patterns and coverage check with given type?
  -> [Clause]
  -> TCM (Maybe SplitTree, Bool, CompiledClauses)
     -- ^ The 'Bool' indicates whether we turned a record expression into a copattern match.
compileClauses mt cs = do
  -- Construct clauses with pattern variables bound in left-to-right order.
  -- Discard de Bruijn indices in patterns.
  case mt of
    Nothing -> (Nothing,False,) . compile . map unBruijn <$> normaliseProjP cs
    Just (q, t)  -> do
      splitTree <- coverageCheck q t cs

      reportSDoc "tc.cc.tree" 20 $ vcat
        [ "split tree of " <+> prettyTCM q <+> " from coverage check "
        , return $ P.pretty splitTree
        ]

      -- The coverage checker might have added some clauses (#2288)!
      -- Throw away the unreachable clauses (#2723).
      let notUnreachable = (Just True /=) . clauseUnreachable
      cs <- normaliseProjP =<< instantiateFull =<< filter notUnreachable . defClauses <$> getConstInfo q

      let cls = map unBruijn cs

      reportSDoc "tc.cc" 30 $ sep $ do
        ("clauses patterns of " <+> prettyTCM q <+> " before compilation") : do
          map (prettyTCM . map unArg . clPats) cls
      reportSDoc "tc.cc" 50 $
        "clauses of " <+> prettyTCM q <+> " before compilation" <?> pretty cs
      let cc = compileWithSplitTree splitTree cls
      reportSDoc "tc.cc" 20 $ sep
        [ "compiled clauses of " <+> prettyTCM q <+> " (still containing record splits)"
        , nest 2 $ return $ P.pretty cc
        ]
      (cc, becameCopatternLHS) <- runChangeT $ translateCompiledClauses cc
      reportSDoc "tc.cc" 12 $ sep
        [ "compiled clauses of " <+> prettyTCM q
        , nest 2 $ return $ P.pretty cc
        ]
      return (Just splitTree, becameCopatternLHS, fmap precomputeFreeVars_ cc)

-- | Stripped-down version of 'Agda.Syntax.Internal.Clause'
--   used in clause compiler.
data Cl = Cl
  { clPats :: [Arg Pattern]
      -- ^ Pattern variables are considered in left-to-right order.
  , clBody :: Maybe Term
  } deriving (Show)

instance P.Pretty Cl where
  pretty (Cl ps b) = P.prettyList ps P.<+> "->" P.<+> maybe "_|_" P.pretty b

type Cls = [Cl]

-- | Strip down a clause. Don't forget to apply the substitution to the dot
--   patterns!
unBruijn :: Clause -> Cl
unBruijn c = Cl (applySubst sub $ (map . fmap) (fmap dbPatVarName . namedThing) $ namedClausePats c)
                (applySubst sub $ clauseBody c)
  where
    sub = renamingR $ fromMaybe __IMPOSSIBLE__ (clausePerm c)

compileWithSplitTree :: SplitTree -> Cls -> CompiledClauses
compileWithSplitTree t cs = case t of
  SplitAt i lz ts -> Case i $ compiles lz ts $ splitOn (natSize ts == 1) (unArg i) cs
        -- if there is just one case, we force expansion of catch-alls
        -- this is needed to generate a sound tree on which we can
        -- collapse record pattern splits
  SplittingDone n -> compile cs
    -- after end of split tree, continue with left-to-right strategy

  where
    compiles :: LazySplit -> SplitTrees -> Case Cls -> Case CompiledClauses
    compiles lz ts br@Branches{ projPatterns = cop
                              , conBranches = cons
                              , etaBranch   = Nothing
                              , litBranches = lits
                              , fallThrough = fT
                              , catchAllBranch = catchAll
                              , lazyMatch = lazy }
      = br{ conBranches    = updCons cons
          , etaBranch      = Nothing
          , litBranches    = updLits lits
          , fallThrough    = fT
          , catchAllBranch = updCatchall catchAll
          , lazyMatch      = lazy || lz == LazySplit
          }
      where
        updCons = Map.mapWithKey $ \ c cl ->
         caseMaybe (lookup (SplitCon c) ts) compile compileWithSplitTree <$> cl
         -- When the split tree is finished, we continue with @compile@.
        updLits = Map.mapWithKey $ \ l cl ->
          caseMaybe (lookup (SplitLit l) ts) compile compileWithSplitTree cl
        updCatchall = fmap $ caseMaybe (lookup SplitCatchall ts) compile compileWithSplitTree
    compiles _ _ Branches{etaBranch = Just{}} = __IMPOSSIBLE__  -- we haven't inserted eta matches yet

compile :: Cls -> CompiledClauses
compile [] = Fail []
compile cs = case nextSplit cs of
  Just (isRecP, n) -> Case n $ compile <$> splitOn isRecP (unArg n) cs
  Nothing -> case clBody c of
    -- It's possible to get more than one clause here due to
    -- catch-all expansion.
    Just t  -> Done (map (fmap name) $ clPats c) t
    Nothing -> Fail (map (fmap name) $ clPats c)
  where
    -- If there are more than one clauses, take the first one.
    c = headWithDefault __IMPOSSIBLE__ cs
    name (VarP _ x) = x
    name (DotP _ _) = underscore
    name ConP{}  = __IMPOSSIBLE__
    name DefP{}  = __IMPOSSIBLE__
    name LitP{}  = __IMPOSSIBLE__
    name ProjP{} = __IMPOSSIBLE__
    name (IApplyP _ _ _ x) = x

-- | Get the index of the next argument we need to split on.
--   This the number of the first pattern that does a (non-lazy) match in the first clause.
--   Or the first lazy match where all clauses agree on the constructor, if there are no
--   non-lazy matches.
nextSplit :: Cls -> Maybe (Bool, Arg Int)
nextSplit []             = __IMPOSSIBLE__
nextSplit (Cl ps _ : cs) = findSplit nonLazy ps <|> findSplit allAgree ps
  where
    nonLazy _ (ConP _ cpi _) = not $ conPLazy cpi
    nonLazy _ _              = True

    findSplit okPat ps = listToMaybe (catMaybes $
      zipWith (\ (Arg ai p) n -> (, Arg ai n) <$> properSplit p <* guard (okPat n p)) ps [0..])

    allAgree i (ConP c _ _) = all ((== Just (conName c)) . getCon . map unArg . drop i . clPats) cs
    allAgree _ _            = False

    getCon (ConP c _ _ : _) = Just $ conName c
    getCon _                = Nothing

-- | Is is not a variable pattern?
--   And if yes, is it a record pattern and/or a fallThrough one?
properSplit :: Pattern' a -> Maybe Bool
properSplit (ConP _ cpi _) = Just ((conPRecord cpi && patOrigin (conPInfo cpi) == PatORec) || conPFallThrough cpi)
properSplit DefP{}    = Just False
properSplit LitP{}    = Just False
properSplit ProjP{}   = Just False
properSplit IApplyP{} = Nothing
properSplit VarP{}    = Nothing
properSplit DotP{}    = Nothing

-- | Is this a variable pattern?
--
--   Maintain invariant: @isVar = isNothing . properSplit@!
isVar :: Pattern' a -> Bool
isVar IApplyP{} = True
isVar VarP{}    = True
isVar DotP{}    = True
isVar ConP{}    = False
isVar DefP{}    = False
isVar LitP{}    = False
isVar ProjP{}   = False

-- | @splitOn single n cs@ will force expansion of catch-alls
--   if @single@.
splitOn :: Bool -> Int -> Cls -> Case Cls
splitOn single n cs = mconcat $ map (fmap (:[]) . splitC n) $
  -- (\ cs -> trace ("splitting on " ++ show n ++ " after expandCatchAlls " ++ show single ++ ": " ++ prettyShow (P.prettyList cs)) cs) $
    expandCatchAlls single n cs

splitC :: Int -> Cl -> Case Cl
splitC n (Cl ps b) = caseMaybe mp fallback $ \case
  ProjP _ d   -> projCase d $ Cl (ps0 ++ ps1) b
  IApplyP{}   -> fallback
  ConP c i qs -> (conCase (conName c) (conPFallThrough i) $ WithArity (length qs) $
                   Cl (ps0 ++ map (fmap namedThing) qs ++ ps1) b) { lazyMatch = conPLazy i }
  DefP o q qs -> (conCase q False $ WithArity (length qs) $
                   Cl (ps0 ++ map (fmap namedThing) qs ++ ps1) b) { lazyMatch = False }
  LitP _ l    -> litCase l $ Cl (ps0 ++ ps1) b
  VarP{}      -> fallback
  DotP{}      -> fallback
  where
    (ps0, rest) = splitAt n ps
    mp          = unArg <$> listToMaybe rest
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
--
-- Example from issue #3628:
-- @
--   f i j k (i = i0)(k = i1) = base
--   f i j k (j = i1)         = base
-- @
-- case tree:
-- @
--   f i j k o = case i of
--     i0 -> case k of
--             i1 -> base
--             _  -> case j of
--                     i1 -> base
--     _  -> case j of
--             i1 -> base
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

    classify (LitP _ l)   = Left l
    classify (ConP c _ _) = Right (Left c)
    classify (DefP _ q _) = Right (Right q)
    classify _            = __IMPOSSIBLE__

    -- All non-catch-all patterns following this one (at position n).
    -- These are the cases the wildcard needs to be expanded into.
    expansions = nubOn (classify . unArg . snd)
               . mapMaybe (notVarNth . clPats)
               $ cs
    notVarNth
      :: [Arg Pattern]
      -> Maybe ([Arg Pattern]  -- First @n@ patterns.
               , Arg Pattern)  -- @n+1@st pattern, not a variable
    notVarNth ps = do
      let (ps1, ps2) = splitAt n ps
      p <- listToMaybe ps2
      guard $ not $ isVar $ unArg p
      return (ps1, p)

    expand cl (qs, q) =
      case unArg q of
        ConP c mt qs' -> Cl (ps0 ++ [q $> ConP c mt conPArgs] ++ ps1)
                            (substBody n' m (Con c ci (map Apply conArgs)) b)
          where
            ci       = fromConPatternInfo mt
            m        = length qs'
            -- replace all direct subpatterns of q by _
            -- TODO Andrea: might need these to sometimes be IApply?
            conPArgs = map (fmap ($> varP "_")) qs'
            conArgs  = zipWith (\ q' i -> q' $> var i) qs' $ downFrom m
        LitP i l -> Cl (ps0 ++ [q $> LitP i l] ++ ps1) (substBody n' 0 (Lit l) b)
        DefP o d qs' -> Cl (ps0 ++ [q $> DefP o d conPArgs] ++ ps1)
                            (substBody n' m (Def d (map Apply conArgs)) b)
          where
            m        = length qs'
            -- replace all direct subpatterns of q by _
            conPArgs = map (fmap ($> varP "_")) qs'
            conArgs  = zipWith (\ q' i -> q' $> var i) qs' $ downFrom m
        _ -> __IMPOSSIBLE__
      where
        -- Andreas, 2016-09-19 issue #2168
        -- Due to varying function arity, some clauses might be eta-contracted.
        -- Thus, we eta-expand them.
        Cl ps b = ensureNPatterns (n + 1) (map getArgInfo $ qs ++ [q]) cl
        -- The following pattern match cannot fail (by construction of @ps@).
        (ps0, _:ps1) = splitAt n ps

        n' = countPatternVars ps1

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
  ps'  = for ais $ \ ai -> Arg ai $ varP "_"
  args = zipWith (\ i ai -> Arg ai $ var i) (downFrom m) ais

substBody :: Subst a => Int -> Int -> SubstArg a -> a -> a
substBody n m v = applySubst $ liftS n $ v :# raiseS m

instance PrecomputeFreeVars a => PrecomputeFreeVars (CompiledClauses' a) where
