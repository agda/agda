{-# LANGUAGE CPP, PatternGuards, FlexibleInstances, GeneralizedNewtypeDeriving #-}

-- | Code which replaces pattern matching on record constructors with
-- uses of projection functions.

module Agda.TypeChecking.RecordPatterns
  ( translateRecordPatterns
  , translateSplitTree
  , recordPatternToProjections
  ) where

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad.Fix
import Control.Monad.Reader
import Control.Monad.State

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Traversable as Trav

import Agda.Syntax.Common
import Agda.Syntax.Internal
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
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "../undefined.h"
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
    VarP{}             -> return [ \ x -> x ]
    LitP{}             -> typeError $ ShouldBeRecordPattern p
    DotP{}             -> typeError $ ShouldBeRecordPattern p
    ConP c Nothing  ps -> typeError $ ShouldBeRecordPattern p
    ConP c (Just t) ps -> do
      t <- reduce t
      fields <- getRecordTypeFields (unArg t)
      concat <$> zipWithM comb (map proj fields) (map unArg ps)
  where
    proj p = \ x -> Def (unArg p) [defaultArg x]
    comb :: (Term -> Term) -> Pattern -> TCM [Term -> Term]
    comb prj p = map (prj .) <$> recordPatternToProjections p

{-
---------------------------------------------------------------------------
-- * Record pattern translation for compiled clauses
---------------------------------------------------------------------------

translateCompiledRecordPatterns :: CompiledClauses -> TCM CompiledClauses
translateCompiledRecordPatterns cc = loop 0 [] cc
  where
    loop n vs cc = case cc of
      Case i cs -> do
        isRC <- isRecordCase cs
        case isRC of
          Nothing ->

-- | @replaceByProjections i projs cc@ replaces variables @i..i+n-1@
--   (counted from left) by projections @projs_1 i .. projs_n i@.
--
--   If @n==0@, we matched on a zero-field record, which means that
--   we are actually introduce a new variable, increasing split
--   positions greater or equal to @i@ by one.
--   Otherwise, we have to lower
--
replaceByProjections :: Int -> [QName] -> CompiledClauses -> TCM CompiledClauses
replaceByProjections i projs cc = do
  let n = length projs
      loop i cc = case cc of
        Case j cs

        -- if j < i, we leave j untouched, but we increase i by the number
        -- of variables replacing j in the branches
          | j < i -> Case j

        -- if j >= i then we shrink j by (n-1)
          | j >= i -> Case (j - (n-1)) <$> Trav.mapM (loop i) cs

        Done xs v ->
        -- we have to delete (n-1) variables from xs
        -- and instantiate v suitably with the projections

        Fail -> return Fail

  loop i cc

-- | Check if a split is on a record constructor, and return the projections
--   if yes.
isRecordCase :: Case c -> TCM (Maybe ([QName], c))
isRecordCase (Branches { conBranches = conMap
                       , litBranches = litMap
                       , catchAllBranch = Nothing })
  | Map.null litBranches
  , [(con,br)] <- Map.toList conMap = do
    isRC <- isRecordConstructor con
    case isRC of
      Just (r, Record { recFields = fs }) -> return $ Just (map unArg fs, br)
      Just (r, _) -> __IMPOSSIBLE__
      Nothing -> return Nothing
isRecordCase _ = return Nothing
-}

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
          (isRC, n) <- getConstructorArity c
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

    loops :: Int -> SplitTrees -> TCM (Bool, [Bool], SplitTrees)
    loops i ts = do
      -- note: ts not empty
      (rs, xss, ts) <- unzip3 <$> do
        forM ts $ \ (c, t) -> do
          (xs, t) <- loop t
          (isRC, n) <- getConstructorArity c
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
      return (x, foldl1 (zipWith (&&)) xss, ts)

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

  (ps, s, cs) <- runRecPatM $ translatePatterns $ clausePats clause

  let -- Number of variables + dot patterns in new clause.
      noNewPatternVars = size cs

      s'   = reverse s
      mkSub s = foldr (:#) (raiseS noNewPatternVars) s

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
        permute (invertP $ compactP $ clausePerm clause) $
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
            { clauseTel  = newTel
            , clausePerm = newPerm
            , clausePats = applySubst lhsSubst ps
            , clauseBody = translateBody cs rhsSubst $ clauseBody clause
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

type Changes = [Either Pattern (Kind -> Nat, String, Dom Type)]

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
translatePattern (ConP c Nothing ps) = do
  (ps, s, cs) <- translatePatterns ps
  return (ConP c Nothing ps, s, cs)
translatePattern p@(ConP _ (Just _) _) = do
  r <- recordTree p
  case r of
    Left  r -> r
    Right t -> removeTree t
translatePattern p@VarP{} = removeTree (Leaf p)
translatePattern p@DotP{} = removeTree (Leaf p)
translatePattern p@LitP{} = return (p, [], [])

-- | 'translatePattern' lifted to lists of arguments.

translatePatterns ::
  [Arg Pattern] -> RecPatM ([Arg Pattern], [Term], Changes)
translatePatterns ps = do
  (ps', ss, cs) <- unzip3 <$> mapM (translatePattern . unArg) ps
  return (ps' `withArgsFrom` ps, concat ss, concat cs)

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
recordTree p@(ConP _ Nothing _) = return $ Left $ translatePattern p
recordTree (ConP c (Just t) ps) = do
  rs <- mapM (recordTree . unArg) ps
  case allRight rs of
    Left rs ->
      return $ Left $ do
        (ps', ss, cs) <- unzip3 <$> mapM (either id removeTree) rs
        return (ConP c (Just t) (ps' `withArgsFrom` ps),
                concat ss, concat cs)
    Right ts -> liftTCM $ do
      t <- reduce t
      fields <- getRecordTypeFields (unArg t)
      let proj p = \x -> Def (unArg p) [defaultArg x]
      return $ Right $ RecCon t $ zip (map proj fields) ts
recordTree p@VarP{} = return (Right (Leaf p))
recordTree p@DotP{} = return (Right (Leaf p))
recordTree p@LitP{} = return $ Left $ translatePattern p

------------------------------------------------------------------------
-- Translation of the clause telescope and body

-- | Translates the telescope.

translateTel
  :: Changes
     -- ^ Explanation of how the telescope should be changed. Types
     -- should be in the context of the old telescope.
  -> [(String, Dom Type)]
     -- ^ Old telescope, flattened, in textual left-to-right
     -- order.
  -> [Maybe (String, Dom Type)]
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
  foldr (:#) (raiseS (size is)) [ makeVar i | i <- [0..n - 1] ]
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
