
-- | Code which replaces pattern matching on record constructors with
-- uses of projection functions.

module Agda.TypeChecking.RecordPatterns
  ( translateRecordPatterns
  , translateCompiledClauses
  , translateSplitTree
  , recordPatternToProjections
  ) where

import Control.Arrow (first, second)
import Control.Monad.Fix
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.List as List
import Data.Maybe
import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern as I

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty hiding (pretty)
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Permutation hiding (dropFrom)
import Agda.Utils.Pretty (Pretty(..))
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Size
import Agda.Utils.Update (MonadChange, tellDirty)

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Record pattern translation for let bindings
---------------------------------------------------------------------------

-- | Take a record pattern @p@ and yield a list of projections
--   corresponding to the pattern variables, from left to right.
--
--   E.g. for @(x , (y , z))@ we return @[ fst, fst . snd, snd . snd ]@.
--
--   If it is not a record pattern, error 'ShouldBeRecordPattern' is raised.
recordPatternToProjections :: DeBruijnPattern -> TCM [Term -> Term]
recordPatternToProjections p =
  case p of
    VarP{}       -> return [ id ]
    LitP{}       -> typeError $ ShouldBeRecordPattern p
    DotP{}       -> typeError $ ShouldBeRecordPattern p
    ConP c ci ps -> do
      unless (conPRecord ci) $
        typeError $ ShouldBeRecordPattern p
      let t = unArg $ fromMaybe __IMPOSSIBLE__ $ conPType ci
      reportSDoc "tc.rec" 45 $ vcat
        [ "recordPatternToProjections: "
        , nest 2 $ "constructor pattern " <+> prettyTCM p <+> " has type " <+> prettyTCM t
        ]
      reportSLn "tc.rec" 70 $ "  type raw: " ++ show t
      fields <- getRecordTypeFields t
      concat <$> zipWithM comb (map proj fields) (map namedArg ps)
    ProjP{}      -> __IMPOSSIBLE__ -- copattern cannot appear here
    IApplyP{}    -> typeError $ ShouldBeRecordPattern p
    DefP{}       -> typeError $ ShouldBeRecordPattern p
  where
    proj p = (`applyE` [Proj ProjSystem $ unDom p])
    comb :: (Term -> Term) -> DeBruijnPattern -> TCM [Term -> Term]
    comb prj p = map (\ f -> f . prj) <$> recordPatternToProjections p


---------------------------------------------------------------------------
-- * Record pattern translation for compiled clauses
---------------------------------------------------------------------------

-- | Take a matrix of booleans (at least one row!) and summarize the columns
--   using conjunction.
conjColumns :: [[Bool]] -> [Bool]
conjColumns =  foldl1 (zipWith (&&))

-- UNUSED Liang-Ting 2019-07-16
---- | @insertColumn i a m@ inserts a column before the @i@th column in
----   matrix @m@ and fills it with value @a@.
--insertColumn :: Int -> a -> [[a]] -> [[a]]
--insertColumn i a rows = map ins rows where
--  ins row = let (init, last) = splitAt i row in init ++ a : last

{- UNUSED
-- | @cutColumn i m@ removes the @i@th column from matrix @m@.
cutColumn :: Int -> [[a]] -> [[a]]
cutColumn i rows = map cut rows where
  cut row = let (init, _:last) = splitAt i row in init ++ last

-- | @cutColumns i n xss = (yss, xss')@ cuts out a submatrix @yss@
--   of width @n@ from @xss@, starting at column @i@.
cutColumns :: Int -> Int -> [[a]] -> ([[a]], [[a]])
cutColumns i n rows = unzip (map (cutSublist i n) rows)
-}

-- UNUSED Liang-Ting 2019-07-16
---- | @cutSublist i n xs = (xs', ys, xs'')@ cuts out a sublist @ys@
----   of width @n@ from @xs@, starting at column @i@.
--cutSublist :: Int -> Int -> [a] -> ([a], [a], [a])
--cutSublist i n row =
--  let (init, rest) = splitAt i row
--      (mid , last) = splitAt n rest
--  in  (init, mid, last)

getEtaAndArity :: SplitTag -> TCM (Bool, Nat)
getEtaAndArity (SplitCon c) =
  for (getConstructorInfo c) $ \case
    DataCon n        -> (False, n)
    RecordCon _ eta fs -> (eta == YesEta, size fs)
getEtaAndArity (SplitLit l) = return (False, 0)
getEtaAndArity SplitCatchall = return (False, 1)

translateCompiledClauses
  :: forall m. (HasConstInfo m, MonadChange m)
  => CompiledClauses -> m CompiledClauses
translateCompiledClauses cc = ignoreAbstractMode $ do
  reportSDoc "tc.cc.record" 20 $ vcat
    [ "translate record patterns in compiled clauses"
    , nest 2 $ return $ pretty cc
    ]
  cc <- loop cc
  reportSDoc "tc.cc.record" 20 $ vcat
    [ "translated compiled clauses (no eta record patterns):"
    , nest 2 $ return $ pretty cc
    ]
  cc <- recordExpressionsToCopatterns cc
  reportSDoc "tc.cc.record" 20 $ vcat
    [ "translated compiled clauses (record expressions to copatterns):"
    , nest 2 $ return $ pretty cc
    ]
  return cc
  where

    loop :: CompiledClauses -> m (CompiledClauses)
    loop cc = case cc of
      Fail{}    -> return cc
      Done{}    -> return cc
      Case i cs -> loops i cs

    loops :: Arg Int               -- split variable
          -> Case CompiledClauses  -- original split tree
          -> m CompiledClauses
    loops i cs@Branches{ projPatterns   = comatch
                       , conBranches    = conMap
                       , etaBranch      = eta
                       , litBranches    = litMap
                       , fallThrough    = fT
                       , catchAllBranch = catchAll
                       , lazyMatch      = lazy } = do

      catchAll <- traverse loop catchAll
      litMap   <- traverse loop litMap
      (conMap, eta) <- do
        let noEtaCase = (, Nothing) <$> (traverse . traverse) loop conMap
            yesEtaCase b ch = (Map.empty,) . Just . (ch,) <$> traverse loop b
        case Map.toList conMap of
              -- This is already an eta match. Still need to recurse though.
              -- This can happen (#2981) when we
              -- 'revisitRecordPatternTranslation' in Rules.Decl, due to
              -- inferred eta.
          _ | Just (ch, b) <- eta -> yesEtaCase b ch
          [(c, b)] | not comatch -> -- possible eta-match
            getConstructorInfo' c >>= \ case
              Just (RecordCon pm YesEta fs) -> yesEtaCase b $
                ConHead c (IsRecord pm) Inductive (map argFromDom fs)
              _ -> noEtaCase
          _ -> noEtaCase
      return $ Case i cs{ conBranches    = conMap
                        , etaBranch      = eta
                        , litBranches    = litMap
                        , fallThrough    = fT
                        , catchAllBranch = catchAll
                        }

{- UNUSED
instance Monoid CompiledClauses where
  mempty = __IMPOSSIBLE__
  mappend (Case n c) (Case n' c') | n == n' = Case n $ mappend c c'
  mappend _ _ = __IMPOSSIBLE__

mergeCatchAll :: CompiledClauses -> Maybe CompiledClauses -> CompiledClauses
mergeCatchAll cc ca = maybe cc (mappend cc) ca
{-
  case (cc, ca) of
    (_       , Nothing) -> cc
    (Case n c, Just (Case n' c')) | n == n' -> Case n $ mappend c c'
    _                   -> __IMPOSSIBLE__ -- this would mean non-determinism
-}
-}

-- | Transform definitions returning record expressions to use copatterns
--   instead. This prevents terms from blowing up when reduced.
recordExpressionsToCopatterns
  :: (HasConstInfo m, MonadChange m)
  => CompiledClauses
  -> m CompiledClauses
recordExpressionsToCopatterns = \case
    Case i bs -> Case i <$> traverse recordExpressionsToCopatterns bs
    cc@Fail{} -> return cc
    cc@(Done xs (Con c ConORec es)) -> do  -- don't translate if using the record /constructor/
      let vs = map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      Constructor{ conArity = ar } <- theDef <$> getConstInfo (conName c)
      irrProj <- optIrrelevantProjections <$> pragmaOptions
      getConstructorInfo (conName c) >>= \ case
        RecordCon CopatternMatching YesEta fs
          | ar <- length fs, ar > 0,                   -- only for eta-records with at least one field
            length vs == ar,                           -- where the constructor application is saturated
            irrProj || not (any isIrrelevant fs) -> do -- and irrelevant projections (if any) are allowed
              tellDirty
              Case (defaultArg $ length xs) <$> do
                -- translate new cases recursively (there might be nested record expressions)
                traverse recordExpressionsToCopatterns $ Branches
                  { projPatterns   = True
                  , conBranches    = Map.fromListWith __IMPOSSIBLE__ $
                      zipWith (\ f v -> (unDom f, WithArity 0 $ Done xs v)) fs vs
                  , etaBranch      = Nothing
                  , litBranches    = Map.empty
                  , catchAllBranch = Nothing
                  , fallThrough    = Nothing
                  , lazyMatch      = False
                  }
        _ -> return cc
    cc@Done{} -> return cc

-- UNUSED Liang-Ting Chen 2019-07-16
---- | @replaceByProjections i projs cc@ replaces variables @i..i+n-1@
----   (counted from left) by projections @projs_1 i .. projs_n i@.
----
----   If @n==0@, we matched on a zero-field record, which means that
----   we are actually introduce a new variable, increasing split
----   positions greater or equal to @i@ by one.
----   Otherwise, we have to lower
----
--replaceByProjections :: Arg Int -> [QName] -> CompiledClauses -> CompiledClauses
--replaceByProjections (Arg ai i) projs cc =
--  let n = length projs
--
--      loop :: Int -> CompiledClauses -> CompiledClauses
--      loop i cc = case cc of
--        Case j cs
--
--        -- if j < i, we leave j untouched, but we increase i by the number
--        -- of variables replacing j in the branches
--          | unArg j < i -> Case j $ loops i cs
--
--        -- if j >= i then we shrink j by (n-1)
--          | otherwise   -> Case (j <&> \ k -> k - (n-1)) $ fmap (loop i) cs
--
--        Done xs v ->
--        -- we have to delete (n-1) variables from xs
--        -- and instantiate v suitably with the projections
--          let (xs0,xs1,xs2)     = cutSublist i n xs
--              names | null xs1  = ["r"]
--                    | otherwise = map unArg xs1
--              x                 = Arg ai $ foldr1 appendArgNames names
--              xs'               = xs0 ++ x : xs2
--              us                = map (\ p -> Var 0 [Proj ProjSystem p]) (reverse projs)
--              -- go from level (i + n - 1) to index (subtract from |xs|-1)
--              index             = length xs - (i + n)
--          in  Done xs' $ applySubst (liftS (length xs2) $ us ++# raiseS 1) v
--          -- The body is NOT guarded by lambdas!
--          -- WRONG: underLambdas i (flip apply) (map defaultArg us) v
--
--        Fail -> Fail
--
--      loops :: Int -> Case CompiledClauses -> Case CompiledClauses
--      loops i bs@Branches{ conBranches    = conMap
--                         , litBranches    = litMap
--                         , catchAllBranch = catchAll } =
--        bs{ conBranches    = fmap (\ (WithArity n c) -> WithArity n $ loop (i + n - 1) c) conMap
--          , litBranches    = fmap (loop (i - 1)) litMap
--          , catchAllBranch = fmap (loop i) catchAll
--          }
--  in  loop i cc

-- UNUSED Liang-Ting 2019-07-16
---- | Check if a split is on a record constructor, and return the projections
----   if yes.
--isRecordCase :: Case c -> TCM (Maybe ([QName], c))
--isRecordCase (Branches { conBranches = conMap
--                       , litBranches = litMap
--                       , catchAllBranch = Nothing })
--  | Map.null litMap
--  , [(con, WithArity _ br)] <- Map.toList conMap = do
--    isRC <- isRecordConstructor con
--    case isRC of
--      Just (r, Record { recFields = fs }) -> return $ Just (map unArg fs, br)
--      Just (r, _) -> __IMPOSSIBLE__
--      Nothing -> return Nothing
--isRecordCase _ = return Nothing

---------------------------------------------------------------------------
-- * Record pattern translation for split trees
---------------------------------------------------------------------------
--UNUSED Liang-Ting Chen 2019-07-16
---- | Split tree annotation.
--data RecordSplitNode = RecordSplitNode
--  { _splitTag           :: SplitTag -- ^ Constructor name/literal for this branch.
--  , _splitArity         :: Int      -- ^ Arity of the constructor.
--  , _splitRecordPattern :: Bool     -- ^ Should we translate this split away?
--  }

-- | Split tree annotated for record pattern translation.
--type RecordSplitTree  = SplitTree' RecordSplitNode
--type RecordSplitTrees = SplitTrees' RecordSplitNode

--UNUSED Liang-Ting Chen 2019-07-16
---- | Bottom-up procedure to annotate split tree.
--recordSplitTree :: SplitTree -> TCM RecordSplitTree
--recordSplitTree = snd <.> loop
--  where
--
--    loop :: SplitTree -> TCM ([Bool], RecordSplitTree)
--    loop = \case
--      SplittingDone n -> return (replicate n True, SplittingDone n)
--      SplitAt i ts    -> do
--        (xs, ts) <- loops (unArg i) ts
--        return (xs, SplitAt i ts)
--
--    loops :: Int -> SplitTrees -> TCM ([Bool], RecordSplitTrees)
--    loops i ts = do
--      (xss, ts) <- unzip <$> do
--        forM ts $ \ (c, t) -> do
--          (xs, t) <- loop t
--          (isRC, n) <- getEtaAndArity c
--          let (xs0, rest) = splitAt i xs
--              (xs1, xs2)  = splitAt n rest
--              x           = isRC && and xs1
--              xs'         = xs0 ++ x : xs2
--          return (xs, (RecordSplitNode c n x, t))
--      return (foldl1 (zipWith (&&)) xss, ts)

-- | Bottom-up procedure to record-pattern-translate split tree.
translateSplitTree :: SplitTree -> TCM SplitTree
translateSplitTree = snd <.> loop
  where

    -- @loop t = return (xs, t')@ returns the translated split tree @t'@
    -- plus the status @xs@ of the clause variables
    --   True  = variable will never be split on in @t'@ (virgin variable)
    --   False = variable will be spilt on in @t'@
    loop :: SplitTree -> TCM ([Bool], SplitTree)
    loop = \case
      SplittingDone n ->
        -- start with n virgin variables
        return (replicate n True, SplittingDone n)
      SplitAt i lz ts    -> do
        (x, xs, ts) <- loops (unArg i) ts
        -- if we case on record constructor, drop case
        let t' = if x then
                   case ts of
                     [(c,t)] -> t
                     _       -> __IMPOSSIBLE__
                  -- else retain case
                  else SplitAt i lz ts
        return (xs, t')

    -- @loops i ts = return (x, xs, ts')@ cf. @loop@
    -- @x@ says wether at arg @i@ we have a record pattern split
    -- that can be removed
    loops :: Int -> SplitTrees -> TCM (Bool, [Bool], SplitTrees)
    loops i ts = do
      -- note: ts not empty
      (rs, xss, ts) <- unzip3 <$> do
        forM ts $ \ (c, t) -> do
          (xs, t) <- loop t
          (isRC, n) <- getEtaAndArity c
          -- now drop variables from i to i+n-1
          let (xs0, rest) = splitAt i xs
              (xs1, xs2)  = splitAt n rest
              -- if all dropped variables are virgins and we are record cons.
              -- then new variable x is also virgin
              -- and we can translate away the split
              x           = isRC && and xs1
              -- xs' = updated variables
              xs'         = xs0 ++ x : xs2
              -- delete splits from t if record match
              t'          = if x then dropFrom i (n - 1) t else t
          return (x, xs', (c, t'))
      -- x = did we split on a record constructor?
      let x = and rs
      -- invariant: if record constructor, then exactly one constructor
      if x then unless (rs == [True]) __IMPOSSIBLE__
      -- else no record constructor
       else when (or rs) __IMPOSSIBLE__
      return (x, conjColumns xss, ts)

-- | @dropFrom i n@ drops arguments @j@  with @j < i + n@ and @j >= i@.
--   NOTE: @n@ can be negative, in which case arguments are inserted.
class DropFrom a where
  dropFrom :: Int -> Int -> a -> a

instance DropFrom (SplitTree' c) where
  dropFrom i n = \case
    SplittingDone m -> SplittingDone (m - n)
    SplitAt x@(Arg ai j) lz ts
      | j >= i + n -> SplitAt (Arg ai $ j - n) lz $ dropFrom i n ts
      | j < i      -> SplitAt x lz $ dropFrom i n ts
      | otherwise  -> __IMPOSSIBLE__

instance DropFrom (c, SplitTree' c) where
  dropFrom i n (c, t) = (c, dropFrom i n t)

instance DropFrom a => DropFrom [a] where
  dropFrom i n ts = map (dropFrom i n) ts

{-
-- | Check if a split is on a record constructor, and return the projections
--   if yes.
isRecordSplit :: SplitTrees -> TCM (Maybe ([QName], c))
isRecordSplit (Branches { conBranches = conMap
                       , litBranches = litMap
                       , catchAllBranch = Nothing })
  | Map.null litBranches
  , [(con,br)] <- Map.toList conMap = do
    isRC <- isRecordConstructor con
    case isRC of
      Just (r, Record { recFields = fs }) -> return $ Just (map unArg fs, br)
      Just (r, _) -> __IMPOSSIBLE__
      Nothing -> return Nothing
isRecordSplit _ = return Nothing

-}


---------------------------------------------------------------------------
-- * Record pattern translation for function definitions
---------------------------------------------------------------------------

-- | Replaces pattern matching on record constructors with uses of
-- projection functions. Does not remove record constructor patterns
-- which have sub-patterns containing non-record constructor or
-- literal patterns.

translateRecordPatterns :: Clause -> TCM Clause
translateRecordPatterns clause = do
  -- ps: New patterns, in left-to-right order, in the context of the
  -- old RHS.

  -- s: Partial substitution taking the old pattern variables
  -- (including dot patterns; listed from left to right) to terms in
  -- the context of the new RHS.

  -- cs: List of changes, with types in the context of the old
  -- telescope.

  (ps, s, cs) <- runRecPatM $ translatePatterns $ unnumberPatVars $ namedClausePats clause

  let -- Number of variables + dot patterns in new clause.
      noNewPatternVars = size cs

      s'   = reverse s
      mkSub s = s ++# raiseS noNewPatternVars

      -- Substitution used to convert terms in the old RHS's
      -- context to terms in the new RHS's context.
      rhsSubst = mkSub s' -- NB:: Defined but not used

      -- Substitution used to convert terms in the old telescope's
      -- context to terms in the new RHS's context.
      perm = fromMaybe __IMPOSSIBLE__ $ clausePerm clause
      rhsSubst' = mkSub $ permute (reverseP perm) s'
      -- TODO: Is it OK to replace the definition above with the
      -- following one?
      --
      --   rhsSubst' = mkSub $ permute (clausePerm clause) s

      -- The old telescope, flattened and in textual left-to-right
      -- order (i.e. the type signature for the variable which occurs
      -- first in the list of patterns comes first).
      flattenedOldTel =
        permute (invertP __IMPOSSIBLE__ $ compactP perm) $
        zip (teleNames $ clauseTel clause) $
        flattenTel $
        clauseTel clause

      -- The new telescope, still flattened, with types in the context
      -- of the new RHS, in textual left-to-right order, and with
      -- Nothing in place of dot patterns.
      substTel = map . fmap . second . applySubst
      newTel' =
        substTel rhsSubst' $
        translateTel cs $
        flattenedOldTel

      -- Permutation taking the new variable and dot patterns to the
      -- new telescope.
      newPerm = adjustForDotPatterns $
                  reorderTel_ $ map (maybe __DUMMY_DOM__ snd) newTel'
        -- It is important that __DUMMY_DOM__ does not mention any variable
        -- (see the definition of reorderTel).
        where
        isDotP n = case List.genericIndex cs n of
                     Left DotP{} -> True
                     _           -> False

        adjustForDotPatterns (Perm n is) =
          Perm n (filter (not . isDotP) is)

      -- Substitution used to convert terms in the new RHS's context
      -- to terms in the new telescope's context.
      lhsSubst' = renaming impossible (reverseP newPerm)

      -- Substitution used to convert terms in the old telescope's
      -- context to terms in the new telescope's context.
      lhsSubst = applySubst lhsSubst' rhsSubst'

      -- The new telescope.
      newTel =
        uncurry unflattenTel . unzip $
        map (fromMaybe __IMPOSSIBLE__) $
        permute newPerm $
        substTel lhsSubst' $
        newTel'

      -- New clause.
      c = clause
            { clauseTel       = newTel
            , namedClausePats = numberPatVars __IMPOSSIBLE__ newPerm $ applySubst lhsSubst ps
            , clauseBody      = applySubst lhsSubst $ clauseBody clause
            }

  reportSDoc "tc.lhs.recpat" 20 $ vcat
      [ "Original clause:"
      , nest 2 $ inTopContext $ vcat
        [ "delta =" <+> prettyTCM (clauseTel clause)
        , "pats  =" <+> text (show $ clausePats clause)
        ]
      , "Intermediate results:"
      , nest 2 $ vcat
        [ "ps        =" <+> text (show ps)
        , "s         =" <+> prettyTCM s
        , "cs        =" <+> prettyTCM cs
        , "flattenedOldTel =" <+> (text . show) flattenedOldTel
        , "newTel'   =" <+> (text . show) newTel'
        , "newPerm   =" <+> prettyTCM newPerm
        ]
      ]

  reportSDoc "tc.lhs.recpat" 20 $ vcat
        [ "lhsSubst' =" <+> (text . show) lhsSubst'
        , "lhsSubst  =" <+> (text . show) lhsSubst
        , "newTel  =" <+> prettyTCM newTel
        ]

  reportSDoc "tc.lhs.recpat" 10 $
    escapeContext impossible (size $ clauseTel clause) $ vcat
      [ "Translated clause:"
      , nest 2 $ vcat
        [ "delta =" <+> prettyTCM (clauseTel c)
        , "ps    =" <+> text (show $ clausePats c)
        , "body  =" <+> text (show $ clauseBody c)
        , "body  =" <+> addContext (clauseTel c) (maybe "_|_" prettyTCM (clauseBody c))
        ]
      ]

  return c

------------------------------------------------------------------------
-- Record pattern monad

-- | A monad used to translate record patterns.
--
-- The state records the number of variables produced so far, the
-- reader records the total number of variables produced by the entire
-- computation. Functions using this monad need to be sufficiently
-- lazy in the reader component.

newtype RecPatM a = RecPatM (TCMT (ReaderT Nat (StateT Nat IO)) a)
  deriving (Functor, Applicative, Monad,
            MonadIO, MonadTCM, HasOptions,
            MonadTCEnv, MonadTCState)

-- | Runs a computation in the 'RecPatM' monad.

runRecPatM :: RecPatM a -> TCM a
runRecPatM (RecPatM m) =
  mapTCMT (\m -> do
             (x, noVars) <- mfix $ \ ~(_, noVars) ->
                              runStateT (runReaderT m noVars) 0
             return x)
          m

-- | Returns the next pattern variable, and the corresponding term.

nextVar :: RecPatM (Pattern, Term)
nextVar = RecPatM $ do
  n <- lift get
  lift $ put $ succ n
  noVars <- lift ask
  return (varP "r", var $ noVars - n - 1)

------------------------------------------------------------------------
-- Types used to record changes to a clause

-- | @VarPat@ stands for variable patterns, and @DotPat@ for dot
-- patterns.

data Kind = VarPat | DotPat
  deriving Eq

-- | @'Left' p@ means that a variable (corresponding to the pattern
-- @p@, a variable or dot pattern) should be kept unchanged. @'Right'
-- (n, x, t)@ means that @n 'VarPat'@ variables, and @n 'DotPat'@ dot
-- patterns, should be removed, and a new variable, with the name @x@,
-- inserted instead. The type of the new variable is @t@.

type Change  = Either Pattern (Kind -> Nat, ArgName, Dom Type)
type Changes = [Change]

instance Pretty (Kind -> Nat) where
  pretty f =
    ("(VarPat:" P.<+> P.text (show $ f VarPat) P.<+>
    "DotPat:"  P.<+> P.text (show $ f DotPat)) <> ")"

instance PrettyTCM (Kind -> Nat) where
  prettyTCM = return . pretty

instance PrettyTCM Change where
  prettyTCM (Left  p) = prettyTCM p
  prettyTCM (Right (f, x, t)) = "Change" <+> prettyTCM f <+> text x <+> prettyTCM t

-- | Record pattern trees.

data RecordTree
  = Leaf Pattern
    -- ^ Corresponds to variable and dot patterns; contains the
    -- original pattern.
  | RecCon (Arg Type) [(Term -> Term, RecordTree)]
    -- ^ @RecCon t args@ stands for a record constructor application:
    -- @t@ is the type of the application, and the list contains a
    -- projection function and a tree for every argument.

------------------------------------------------------------------------
-- Record pattern trees

-- | @projections t@ returns a projection for every non-dot leaf
-- pattern in @t@. The term is the composition of the projection
-- functions from the leaf to the root.
--
-- Every term is tagged with its origin: a variable pattern or a dot
-- pattern.

projections :: RecordTree -> [(Term -> Term, Kind)]
projections (Leaf (DotP{})) = [(id, DotPat)]
projections (Leaf (VarP{})) = [(id, VarPat)]
projections (Leaf _)        = __IMPOSSIBLE__
projections (RecCon _ args) =
  concatMap (\ (p, t) -> map (first (. p)) $ projections t)
            args

-- | Converts a record tree to a single pattern along with information
-- about the deleted pattern variables.

removeTree :: RecordTree -> RecPatM (Pattern, [Term], Changes)
removeTree tree = do
  (pat, x) <- nextVar
  let ps = projections tree
      s  = map (\(p, _) -> p x) ps

      count k = length $ filter ((== k) . snd) ps

  return $ case tree of
    Leaf p     -> (p,   s, [Left p])
    RecCon t _ -> (pat, s, [Right (count, "r", domFromArg t)])

------------------------------------------------------------------------
-- Translation of patterns

-- | Removes record constructors from patterns.
--
-- Returns the following things:
--
-- * The new pattern.
--
-- * A substitution which maps the /old/ pattern variables (in the
--   order they occurred in the pattern; not including dot patterns)
--   to terms (either the new name of the variable, or a projection
--   applied to a new pattern variable).
--
-- * A list explaining the changes to the variables bound in the
--   pattern.
--
-- Record patterns containing non-record constructor patterns are not
-- translated (though their sub-patterns may be).
--
-- Example: The pattern @rec1 (con1 a) (rec2 b c) (rec3 d)@ should
-- yield the pattern @rec1 (con1 x) y z@, along with a substitution
-- similar to @[x, proj2-1 y, proj2-2 y, proj3-1 z]@.
--
-- This function assumes that literals are never of record type.

translatePattern :: Pattern -> RecPatM (Pattern, [Term], Changes)
translatePattern p@(ConP c ci ps)
  -- Andreas, 2015-05-28 only translate implicit record patterns
  | conPRecord ci , PatOSystem <- patOrigin (conPInfo ci) = do
      r <- recordTree p
      case r of
        Left  r -> r
        Right t -> removeTree t
  | otherwise = do
      (ps, s, cs) <- translatePatterns ps
      return (ConP c ci ps, s, cs)
translatePattern p@(DefP o q ps) = do
      (ps, s, cs) <- translatePatterns ps
      return (DefP o q ps, s, cs)
translatePattern p@VarP{} = removeTree (Leaf p)
translatePattern p@DotP{} = removeTree (Leaf p)
translatePattern p@LitP{} = return (p, [], [])
translatePattern p@ProjP{}= return (p, [], [])
translatePattern p@IApplyP{}= return (p, [], [])

translatePatterns :: [NamedArg Pattern] -> RecPatM ([NamedArg Pattern], [Term], Changes)
translatePatterns ps = do
  (ps', ss, cs) <- unzip3 <$> mapM (translatePattern . namedArg) ps
  return (zipWith (\p -> fmap (p <$)) ps' ps, concat ss, concat cs)

-- | Traverses a pattern and returns one of two things:
--
-- * If there is no non-record constructor in the pattern, then
--   @'Right' ps@ is returned, where @ps@ contains one projection for
--   every variable in the input pattern (in the order they are
--   encountered).
--
-- * Otherwise the output is a computation returning the same kind of
--   result as that coming from 'translatePattern'. (Computations are
--   returned rather than values to ensure that variable numbers are
--   allocated in the right order.)
--
-- Assumes that literals are never of record type.

recordTree ::
  Pattern ->
  RecPatM (Either (RecPatM (Pattern, [Term], Changes)) RecordTree)
-- Andreas, 2015-05-28 only translate implicit record patterns
recordTree p@(ConP c ci ps) | conPRecord ci , PatOSystem <- patOrigin (conPInfo ci) = do
  let t = fromMaybe __IMPOSSIBLE__ $ conPType ci
  rs <- mapM (recordTree . namedArg) ps
  case allRight rs of
    Nothing ->
      return $ Left $ do
        (ps', ss, cs) <- unzip3 <$> mapM (either id removeTree) rs
        return (ConP c ci (ps' `withNamedArgsFrom` ps),
                concat ss, concat cs)
    Just ts -> liftTCM $ do
      t <- reduce t
      reportSDoc "tc.rec" 45 $ vcat
        [ "recordTree: "
        , nest 2 $ "constructor pattern " <+> prettyTCM p <+> " has type " <+> prettyTCM t
        ]
      -- Andreas, 2018-03-03, see #2989:
      -- The content of an @Arg@ might not be reduced (if @Arg@ is @Irrelevant@).
      fields <- getRecordTypeFields =<< reduce (unArg t)
--      let proj p = \x -> Def (unArg p) [defaultArg x]
      let proj p = (`applyE` [Proj ProjSystem $ unDom p])
      return $ Right $ RecCon t $ zip (map proj fields) ts
recordTree p@(ConP _ ci _) = return $ Left $ translatePattern p
recordTree p@DefP{} = return $ Left $ translatePattern p
recordTree p@VarP{} = return (Right (Leaf p))
recordTree p@DotP{} = return (Right (Leaf p))
recordTree p@LitP{} = return $ Left $ translatePattern p
recordTree p@ProjP{}= return $ Left $ translatePattern p
recordTree p@IApplyP{}= return $ Left $ translatePattern p

------------------------------------------------------------------------
-- Translation of the clause telescope and body

-- | Translates the telescope.

translateTel
  :: Changes
     -- ^ Explanation of how the telescope should be changed. Types
     -- should be in the context of the old telescope.
  -> [(ArgName, Dom Type)]
     -- ^ Old telescope, flattened, in textual left-to-right
     -- order.
  -> [Maybe (ArgName, Dom Type)]
     -- ^ New telescope, flattened, in textual left-to-right order.
     -- 'Nothing' is used to indicate the locations of dot patterns.
translateTel (Left (DotP{}) : rest)   tel = Nothing : translateTel rest tel
translateTel (Right (n, x, t) : rest) tel = Just (x, t) :
                                              translateTel rest
                                                (drop (n VarPat) tel)
translateTel (Left _ : rest) (t : tel)    = Just t : translateTel rest tel
translateTel []              []           = []
translateTel (Left _ : _)    []           = __IMPOSSIBLE__
translateTel []              (_ : _)      = __IMPOSSIBLE__
