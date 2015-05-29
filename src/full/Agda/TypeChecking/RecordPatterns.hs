-- GHC 7.4.2 requires this layout for the pragmas. See Issue 1460.
{-# LANGUAGE CPP,
             FlexibleInstances,
             GeneralizedNewtypeDeriving,
             PatternGuards,
             TupleSections #-}

-- | Code which replaces pattern matching on record constructors with
-- uses of projection functions.

module Agda.TypeChecking.RecordPatterns
  ( translateRecordPatterns
  , translateCompiledClauses
  , translateSplitTree
  , recordPatternToProjections
  ) where

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad.Fix
import Control.Monad.Reader
import Control.Monad.State

import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Traversable as Trav

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Either
import Agda.Utils.List
import qualified Agda.Utils.Map as Map
import Agda.Utils.Maybe
import Agda.Utils.Permutation hiding (dropFrom)
import Agda.Utils.Size

#include "undefined.h"
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
recordPatternToProjections :: Pattern -> TCM [Term -> Term]
recordPatternToProjections p =
  case p of
    VarP{}       -> return [ \ x -> x ]
    LitP{}       -> typeError $ ShouldBeRecordPattern p
    DotP{}       -> typeError $ ShouldBeRecordPattern p
    ConP c ci ps -> do
      unless (isJust $ conPRecord ci) $
        typeError $ ShouldBeRecordPattern p
      t <- reduce $ fromMaybe __IMPOSSIBLE__ $ conPType ci
      fields <- getRecordTypeFields (unArg t)
      concat <$> zipWithM comb (map proj fields) (map namedArg ps)
    ProjP{}      -> __IMPOSSIBLE__ -- copattern cannot appear here
  where
    proj p = (`applyE` [Proj $ unArg p])
--    proj p = \ x -> Def (unArg p) [defaultArg x]
    comb :: (Term -> Term) -> Pattern -> TCM [Term -> Term]
    comb prj p = map (\ f -> f . prj) <$> recordPatternToProjections p


---------------------------------------------------------------------------
-- * Record pattern translation for compiled clauses
---------------------------------------------------------------------------

-- | Take a matrix of booleans (at least one row!) and summarize the columns
--   using conjunction.
conjColumns :: [[Bool]] -> [Bool]
conjColumns =  foldl1 (zipWith (&&))

-- | @insertColumn i a m@ inserts a column before the @i@th column in
--   matrix @m@ and fills it with value @a@.
insertColumn :: Int -> a -> [[a]] -> [[a]]
insertColumn i a rows = map ins rows where
  ins row = let (init, last) = splitAt i row in init ++ a : last

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

-- | @cutSublist i n xs = (xs', ys, xs'')@ cuts out a sublist @ys@
--   of width @n@ from @xs@, starting at column @i@.
cutSublist :: Int -> Int -> [a] -> ([a], [a], [a])
cutSublist i n row =
  let (init, rest) = splitAt i row
      (mid , last) = splitAt n rest
  in  (init, mid, last)


translateCompiledClauses :: CompiledClauses -> TCM CompiledClauses
translateCompiledClauses cc = snd <$> loop cc
  where

    loop :: CompiledClauses -> TCM ([Bool], CompiledClauses)
    loop cc = case cc of
      Fail      -> return (repeat True, cc)
      Done xs t -> return (map (const True) xs, cc)
      Case i cs -> loops i cs

    loops :: Int                  -- split variable
          -> Case CompiledClauses -- original split tree
          -> TCM ([Bool], CompiledClauses)
    loops i cs@(Branches { conBranches = conMap
                         , litBranches = litMap
                         , catchAllBranch = catchAll }) = do

      -- recurse on and compute variable status of catch-all clause
      (xssa, catchAll) <- unzipMaybe <$> Trav.mapM loop catchAll
      let xsa = maybe (repeat True) id xssa

      -- recurse on compute variable status of literal clauses
      (xssl, litMap)   <- Map.unzip <$> Trav.mapM loop litMap
      let xsl = conjColumns (xsa : insertColumn i False (Map.elems xssl))

      -- recurse on constructor clauses
      (ccs, xssc, conMap)    <- Map.unzip3 <$> do
        Trav.forM (Map.mapWithKey (,) conMap) $ \ (c, WithArity ar cc) -> do
          (xs, cc)     <- loop cc
--          dataOrRecCon <- getConstructorArity c  -- TODO: c could be a projection
          dataOrRecCon <- do
            isProj <- isProjection c
            case isProj of
               Nothing -> getConstructorArity c
               Just{}  -> return $ Left 0
          let (isRC, n)   = either (False,) ((True,) . size) dataOrRecCon
              (xs0, rest) = genericSplitAt i xs
              (xs1, xs2 ) = genericSplitAt n rest
              -- if all dropped variables (xs1) are virgins and we are record cons.
              -- then new variable x is also virgin
              -- and we can translate away the split
              x           = isRC && and xs1
              -- xs' = updated variables
              xs'         = xs0 ++ x : xs2
              -- get the record fields
              fs          = either __IMPOSSIBLE__ id dataOrRecCon
              -- if x we can translate
              mcc = if x then [replaceByProjections i (map unArg fs) cc] else []

          when (n /= ar) __IMPOSSIBLE__
          return (mcc, xs', WithArity ar cc)

      -- compute result
      let xs = conjColumns (xsl : Map.elems xssc)
      case concat $ Map.elems ccs of
        -- case: no record pattern was translated
        []   -> return (xs, Case i $ Branches
                  { conBranches = conMap
                  , litBranches = litMap
                  , catchAllBranch = catchAll })

        -- case: translated away one record pattern
        [cc] -> do
                -- Andreas, 2013-03-22
                -- Due to catch-all-expansion this is actually possible:
                -- -- we cannot have a catch-all if we had a record pattern
                -- whenJust catchAll __IMPOSSIBLE__
                -- We just drop the catch-all clause.  This is safe because
                -- for record patterns we have expanded all the catch-alls.
                return (xs, cc) -- mergeCatchAll cc catchAll)

        -- case: more than one record patterns (impossible)
        _    -> __IMPOSSIBLE__

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

-- | @replaceByProjections i projs cc@ replaces variables @i..i+n-1@
--   (counted from left) by projections @projs_1 i .. projs_n i@.
--
--   If @n==0@, we matched on a zero-field record, which means that
--   we are actually introduce a new variable, increasing split
--   positions greater or equal to @i@ by one.
--   Otherwise, we have to lower
--
replaceByProjections :: Int -> [QName] -> CompiledClauses -> CompiledClauses
replaceByProjections i projs cc =
  let n = length projs

      loop :: Int -> CompiledClauses -> CompiledClauses
      loop i cc = case cc of
        Case j cs

        -- if j < i, we leave j untouched, but we increase i by the number
        -- of variables replacing j in the branches
          | j < i     -> Case j $ loops i cs

        -- if j >= i then we shrink j by (n-1)
          | otherwise -> Case (j - (n-1)) $ fmap (loop i) cs

        Done xs v ->
        -- we have to delete (n-1) variables from xs
        -- and instantiate v suitably with the projections
          let (xs0,xs1,xs2)     = cutSublist i n xs
              names | null xs1  = ["r"]
                    | otherwise = map unArg xs1
              x                 = defaultArg $ foldr1 appendArgNames names
              xs'               = xs0 ++ x : xs2
              us                = map (\ p -> Var 0 [Proj p]) (reverse projs)
--              us                = map (\ p -> Def p [defaultArg $ var 0]) (reverse projs)
              -- go from level (i + n - 1) to index (subtract from |xs|-1)
              index             = length xs - (i + n)
          in  Done xs' $ applySubst (liftS (length xs2) $ us ++# raiseS 1) v
          -- The body is NOT guarded by lambdas!
          -- WRONG: underLambdas i (flip apply) (map defaultArg us) v

        Fail -> Fail

      loops :: Int -> Case CompiledClauses -> Case CompiledClauses
      loops i Branches{ conBranches    = conMap
                      , litBranches    = litMap
                      , catchAllBranch = catchAll } =
        Branches{ conBranches    = fmap (\ (WithArity n c) -> WithArity n $ loop (i + n - 1) c) conMap
                , litBranches    = fmap (loop (i - 1)) litMap
                , catchAllBranch = fmap (loop i) catchAll
                }
  in  loop i cc

-- | Check if a split is on a record constructor, and return the projections
--   if yes.
isRecordCase :: Case c -> TCM (Maybe ([QName], c))
isRecordCase (Branches { conBranches = conMap
                       , litBranches = litMap
                       , catchAllBranch = Nothing })
  | Map.null litMap
  , [(con, WithArity _ br)] <- Map.toList conMap = do
    isRC <- isRecordConstructor con
    case isRC of
      Just (r, Record { recFields = fs }) -> return $ Just (map unArg fs, br)
      Just (r, _) -> __IMPOSSIBLE__
      Nothing -> return Nothing
isRecordCase _ = return Nothing

---------------------------------------------------------------------------
-- * Record pattern translation for split trees
---------------------------------------------------------------------------

-- | Split tree annotation.
data RecordSplitNode = RecordSplitNode
  { splitCon           :: QName  -- ^ Constructor name for this branch.
  , splitArity         :: Int    -- ^ Arity of the constructor.
  , splitRecordPattern :: Bool   -- ^ Should we translate this split away?
  }

-- | Split tree annotated for record pattern translation.
type RecordSplitTree  = SplitTree' RecordSplitNode
type RecordSplitTrees = SplitTrees' RecordSplitNode



-- | Bottom-up procedure to annotate split tree.
recordSplitTree :: SplitTree -> TCM RecordSplitTree
recordSplitTree t = snd <$> loop t
  where

    loop :: SplitTree -> TCM ([Bool], RecordSplitTree)
    loop t = case t of
      SplittingDone n -> return (replicate n True, SplittingDone n)
      SplitAt i ts    -> do
        (xs, ts) <- loops i ts
        return (xs, SplitAt i ts)

    loops :: Int -> SplitTrees -> TCM ([Bool], RecordSplitTrees)
    loops i ts = do
      (xss, ts) <- unzip <$> do
        forM ts $ \ (c, t) -> do
          (xs, t) <- loop t
          (isRC, n) <- either (False,) ((True,) . size) <$> getConstructorArity c
          let (xs0, rest) = genericSplitAt i xs
              (xs1, xs2)  = genericSplitAt n rest
              x           = isRC && and xs1
              xs'         = xs0 ++ x : xs2
          return (xs, (RecordSplitNode c n x, t))
      return (foldl1 (zipWith (&&)) xss, ts)

-- | Bottom-up procedure to record-pattern-translate split tree.
translateSplitTree :: SplitTree -> TCM SplitTree
translateSplitTree t = snd <$> loop t
  where

    -- @loop t = return (xs, t')@ returns the translated split tree @t'@
    -- plus the status @xs@ of the clause variables
    --   True  = variable will never be split on in @t'@ (virgin variable)
    --   False = variable will be spilt on in @t'@
    loop :: SplitTree -> TCM ([Bool], SplitTree)
    loop t = case t of
      SplittingDone n ->
        -- start with n virgin variables
        return (replicate n True, SplittingDone n)
      SplitAt i ts    -> do
        (x, xs, ts) <- loops i ts
        -- if we case on record constructor, drop case
        let t' = if x then
                   case ts of
                     [(c,t)] -> t
                     _       -> __IMPOSSIBLE__
                  -- else retain case
                  else SplitAt i ts
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
          (isRC, n) <- either (False,) ((True,) . size) <$> getConstructorArity c
          -- now drop variables from i to i+n-1
          let (xs0, rest) = genericSplitAt i xs
              (xs1, xs2)  = genericSplitAt n rest
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
       else unless (or rs == False) __IMPOSSIBLE__
      return (x, conjColumns xss, ts)

-- | @dropFrom i n@ drops arguments @j@  with @j < i + n@ and @j >= i@.
--   NOTE: @n@ can be negative, in which case arguments are inserted.
class DropFrom a where
  dropFrom :: Int -> Int -> a -> a

instance DropFrom (SplitTree' c) where
  dropFrom i n t = case t of
    SplittingDone m -> SplittingDone (m - n)
    SplitAt j ts
      | j >= i + n -> SplitAt (j - n) $ dropFrom i n ts
      | j < i      -> SplitAt j $ dropFrom i n ts
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
--
-- If the input clause contains dot patterns inside record patterns,
-- then the translation may yield clauses which are not type-correct.
-- However, we believe that it is safe to use the output as input to
-- 'Agda.TypeChecking.CompiledClause.Compile.compileClauses'. Perhaps
-- it would be better to perform record pattern translation on the
-- compiled clauses instead, but the code below has already been
-- implemented and seems to work.

translateRecordPatterns :: Clause -> TCM Clause
translateRecordPatterns clause = do
  -- ps: New patterns, in left-to-right order, in the context of the
  -- old RHS.

  -- s: Partial substitution taking the old pattern variables
  -- (including dot patterns; listed from left to right) to terms in
  -- the context of the new RHS.

  -- cs: List of changes, with types in the context of the old
  -- telescope.

  (ps, s, cs) <- runRecPatM $ translatePatterns $ namedClausePats clause

  let -- Number of variables + dot patterns in new clause.
      noNewPatternVars = size cs

      s'   = reverse s
      mkSub s = s ++# raiseS noNewPatternVars

      -- Substitution used to convert terms in the old RHS's
      -- context to terms in the new RHS's context.
      rhsSubst = mkSub s'

      -- Substitution used to convert terms in the old telescope's
      -- context to terms in the new RHS's context.
      rhsSubst' = mkSub $ permute (reverseP $ clausePerm clause) s'
      -- TODO: Is it OK to replace the definition above with the
      -- following one?
      --
      --   rhsSubst' = mkSub $ permute (clausePerm clause) s

      -- The old telescope, flattened and in textual left-to-right
      -- order (i.e. the type signature for the variable which occurs
      -- first in the list of patterns comes first).
      flattenedOldTel =
        permute (invertP __IMPOSSIBLE__ $ compactP $ clausePerm clause) $
        zip (teleNames $ clauseTel clause) $
        flattenTel $
        clauseTel clause

      -- The new telescope, still flattened, with types in the context
      -- of the new RHS, in textual left-to-right order, and with
      -- Nothing in place of dot patterns.
      newTel' =
        map (fmap (id *** applySubst rhsSubst')) $
        translateTel cs $
        flattenedOldTel

      -- Permutation taking the new variable and dot patterns to the
      -- new telescope.
      newPerm = adjustForDotPatterns $
                  reorderTel_ $ map (maybe dummy snd) newTel'
        where
        -- It is important that dummy does not mention any variable
        -- (see the definition of reorderTel).
        dummy = dummyDom -- defaultArg (El Prop (Sort Prop))

        isDotP n = case genericIndex cs n of
                     Left DotP{} -> True
                     _           -> False

        adjustForDotPatterns (Perm n is) =
          Perm n (filter (not . isDotP) is)

      -- Substitution used to convert terms in the new RHS's context
      -- to terms in the new telescope's context.
      lhsSubst' = permToSubst (reverseP newPerm)

      -- Substitution used to convert terms in the old telescope's
      -- context to terms in the new telescope's context.
      lhsSubst = applySubst lhsSubst' rhsSubst'

      -- The new telescope.
      newTel =
        uncurry unflattenTel . unzip $
        map (maybe __IMPOSSIBLE__ id) $
        permute newPerm $
        map (fmap (id *** applySubst lhsSubst')) $
        newTel'

      -- New clause.
      c = clause
            { clauseTel       = newTel
            , clausePerm      = newPerm
            , namedClausePats = applySubst lhsSubst ps
            , clauseBody      = translateBody cs rhsSubst $ clauseBody clause
            }

  reportSDoc "tc.lhs.recpat" 10 $
    escapeContext (size $ clauseTel clause) $ vcat
      [ text "Translated clause:"
      , nest 2 $ vcat
        [ text "delta =" <+> prettyTCM (clauseTel c)
        , text "perm  =" <+> text (show $ clausePerm c)
        , text "ps    =" <+> text (show $ clausePats c)
        , text "body  =" <+> text (show $ clauseBody c)
        , text "body  =" <+> prettyTCM (clauseBody c)
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
            MonadIO, MonadTCM,
            MonadReader TCEnv, MonadState TCState)

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
  return (VarP "r", Var (noVars - n - 1) [])

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

type Changes = [Either Pattern (Kind -> Nat, ArgName, I.Dom Type)]

-- | Record pattern trees.

data RecordTree
  = Leaf Pattern
    -- ^ Corresponds to variable and dot patterns; contains the
    -- original pattern.
  | RecCon (I.Arg Type) [(Term -> Term, RecordTree)]
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
  concatMap (\(p, t) -> map (\(p', k) -> (p' . p, k))
                            (projections t))
            args

-- | Converts a record tree to a single pattern along with information
-- about the deleted pattern variables.

removeTree :: RecordTree -> RecPatM (Pattern, [Term], Changes)
removeTree tree = do
  (pat, x) <- nextVar
  let ps = projections tree
      s  = map (\(p, _) -> p x) ps

      count k = genericLength $ filter ((== k) . snd) ps

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
  -- Andreas, 2015-05-28 only translated implicit record patterns
  | Just True <- conPRecord ci = do
      r <- recordTree p
      case r of
        Left  r -> r
        Right t -> removeTree t
  | otherwise = do
      (ps, s, cs) <- translatePatterns ps
      return (ConP c ci ps, s, cs)
translatePattern p@VarP{} = removeTree (Leaf p)
translatePattern p@DotP{} = removeTree (Leaf p)
translatePattern p@LitP{} = return (p, [], [])
translatePattern p@ProjP{}= return (p, [], [])

translatePatterns :: [I.NamedArg Pattern] -> RecPatM ([I.NamedArg Pattern], [Term], Changes)
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
recordTree (ConP c ci ps) | Just True <- conPRecord ci = do
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
      fields <- getRecordTypeFields (unArg t)
--      let proj p = \x -> Def (unArg p) [defaultArg x]
      let proj p = (`applyE` [Proj $ unArg p])
      return $ Right $ RecCon t $ zip (map proj fields) ts
recordTree p@(ConP _ ci _) = return $ Left $ translatePattern p
recordTree p@VarP{} = return (Right (Leaf p))
recordTree p@DotP{} = return (Right (Leaf p))
recordTree p@LitP{} = return $ Left $ translatePattern p
recordTree p@ProjP{}= return $ Left $ translatePattern p

------------------------------------------------------------------------
-- Translation of the clause telescope and body

-- | Translates the telescope.

translateTel
  :: Changes
     -- ^ Explanation of how the telescope should be changed. Types
     -- should be in the context of the old telescope.
  -> [(ArgName, I.Dom Type)]
     -- ^ Old telescope, flattened, in textual left-to-right
     -- order.
  -> [Maybe (ArgName, I.Dom Type)]
     -- ^ New telescope, flattened, in textual left-to-right order.
     -- 'Nothing' is used to indicate the locations of dot patterns.
translateTel (Left (DotP{}) : rest)   tel = Nothing : translateTel rest tel
translateTel (Right (n, x, t) : rest) tel = Just (x, t) :
                                              translateTel rest
                                                (genericDrop (n VarPat) tel)
translateTel (Left _ : rest) (t : tel)    = Just t : translateTel rest tel
translateTel []              []           = []
translateTel (Left _ : _)    []           = __IMPOSSIBLE__
translateTel []              (_ : _)      = __IMPOSSIBLE__

-- | Translates the clause body. The substitution should take things
-- in the context of the old RHS to the new RHS's context.

translateBody :: Changes -> Substitution -> ClauseBody -> ClauseBody
translateBody _                        s NoBody = NoBody
translateBody (Right (n, x, _) : rest) s b      =
  Bind $ Abs x $ translateBody rest s $ dropBinds n' b
  where n' = sum $ map n [VarPat, DotPat]
translateBody (Left _ : rest) s (Bind b)   = Bind $ fmap (translateBody rest s) b
translateBody []              s (Body t)   = Body $ applySubst s t
translateBody _               _ _          = __IMPOSSIBLE__

------------------------------------------------------------------------
-- Helper functions

-- | Turns a permutation into a substitution.

permToSubst :: Permutation -> Substitution
permToSubst (Perm n is) =
  [ makeVar i | i <- [0..n - 1] ] ++# raiseS (size is)
  where
  makeVar i = case genericElemIndex i is of
    Nothing -> __IMPOSSIBLE__
    Just k  -> var k

-- | @dropBinds n b@ drops the initial @n@ occurrences of 'Bind' from @b@.
--
-- Precondition: @b@ has to start with @n@ occurrences of 'Bind'.

dropBinds :: Nat -> ClauseBody -> ClauseBody
dropBinds n b          | n == 0 = b
dropBinds n (Bind b)   | n > 0  = dropBinds (pred n) (absBody b)
dropBinds _ _                   = __IMPOSSIBLE__
