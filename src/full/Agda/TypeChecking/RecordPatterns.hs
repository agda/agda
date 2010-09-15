{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

-- | Code which replaces pattern matching on record constructors with
-- uses of projection functions.

module Agda.TypeChecking.RecordPatterns
  ( translateRecordPatterns
  ) where

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad.Fix
import Control.Monad.Reader
import Control.Monad.State
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute hiding (Subst)
import Agda.TypeChecking.Telescope
import Agda.Utils.Either
import Agda.Utils.List
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Replaces pattern matching on record constructors with uses of
-- projection functions. Does not remove record constructor patterns
-- which have sub-patterns containing non-record constructor or
-- literal patterns.

translateRecordPatterns :: MonadTCM tcm => Clause -> tcm Clauses
translateRecordPatterns clause = do
  -- ps: New patterns, in left-to-right order, in the context of the
  -- old RHS.

  -- s: Partial substitution taking the old pattern variables
  -- (including dot patterns; listed from left to right) to terms in
  -- the context of the new RHS. The terms are functions expecting a
  -- substitution taking things in the old telescope's context to the
  -- context of the new RHS.

  -- cs: List of changes, with types in the context of the old
  -- telescope.

  (ps, s, cs) <- runRecPatM $ translatePatterns $ clausePats clause

  let -- Number of variables + dot patterns in new clause.
      noNewPatternVars = size cs

      -- Substitution used to convert terms in the old RHS's
      -- context to terms in the new RHS's context.
      rhsSubst = map (\t -> t rhsSubst') (reverse s) ++
                 [ Var i [] | i <- [noNewPatternVars..] ]

      -- Substitution used to convert terms in the old telescope's
      -- context to terms in the new RHS's context.
      rhsSubst' = permute (reverseP $ clausePerm clause) init ++ rest
        where (init, rest) = genericSplitAt (size s) rhsSubst

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
        map (fmap (id *** substs rhsSubst')) $
        translateTel cs $
        flattenedOldTel

      -- Permutation taking the new variable and dot patterns to the
      -- new telescope.
      newPerm = adjustForDotPatterns $
                  reorderTel $ map (maybe dummy snd) newTel'
        where
        -- It is important that dummy does not mention any variable
        -- (see the definition of reorderTel).
        dummy = defaultArg (El Prop (Sort Prop))

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
      lhsSubst = map (substs lhsSubst') rhsSubst'

      -- The new telescope.
      newTel =
        uncurry unflattenTel . unzip $
        map (maybe __IMPOSSIBLE__ id) $
        permute newPerm $
        map (fmap (id *** substs lhsSubst')) $
        newTel'

      -- New clause.
      c = clause
            { clauseTel  = newTel
            , clausePerm = newPerm
            , clausePats = substs lhsSubst ps
            , clauseBody = translateBody cs rhsSubst $ clauseBody clause
            }

  reportSDoc "tc.lhs.top" 10 $
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

  return $ Clauses { translatedClause    = c
                   , maybeOriginalClause =
                       if all isLeft cs then Nothing else Just clause
                   }

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

runRecPatM :: MonadTCM tcm => RecPatM a -> tcm a
runRecPatM (RecPatM m) = liftTCM $
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

-- | Substitutions (with a twist).
--
-- Some parts of the terms building up the substitution need to have a
-- substitution applied to them (in fact, a variant of the
-- substitution itself), so a functional representation is used.

type Subst = [Substitution -> Term]

-- | @'Left' p@ means that a variable (corresponding to the pattern
-- @p@, a variable or dot pattern) should be kept unchanged. @'Right'
-- (n, x, t)@ means that @n 'VarPat'@ variables, and @n 'DotPat'@ dot
-- patterns, should be removed, and a new variable, with the name @x@,
-- inserted instead. The type of the new variable is @t@.

type Changes = [Either Pattern (Kind -> Nat, String, Arg Type)]

-- | Record pattern trees.

data RecordTree
  = Leaf Pattern
    -- ^ Corresponds to variable and dot patterns; contains the
    -- original pattern.
  | RecCon (Arg Type) [(Substitution -> Term -> Term, RecordTree)]
    -- ^ @RecCon t args@ stands for a record constructor application:
    -- @t@ is the type of the application, and the list contains a
    -- projection function (parametrised on a substitution) and a tree
    -- for every argument.

------------------------------------------------------------------------
-- Record pattern trees

-- | @projections t@ returns a projection (parametrised on a
-- substitution) for every non-dot leaf pattern in @t@. The term is
-- the composition of the projection functions from the leaf to the
-- root. The substitution is used to build the individual projection
-- functions.
--
-- Every term is tagged with its origin: a variable pattern or a dot
-- pattern.

projections :: RecordTree -> [(Substitution -> Term -> Term, Kind)]
projections (Leaf (DotP{})) = [(flip const, DotPat)]
projections (Leaf (VarP{})) = [(flip const, VarPat)]
projections (Leaf _)        = __IMPOSSIBLE__
projections (RecCon _ args) =
  concatMap (\(p, t) -> map (\(t, k) -> (\s -> t s . p s, k))
                            (projections t))
            args

-- | Converts a record tree to a single pattern along with information
-- about the deleted pattern variables.
--
-- Raises an error if the tree contains dot patterns inside record
-- patterns.

removeTree :: RecordTree -> RecPatM (Pattern, Subst, Changes)
removeTree tree = do
  (pat, x) <- nextVar
  let ps = projections tree
      s  = map (\(p, _) -> \s -> p s x) ps

      count k = genericLength $ filter ((== k) . snd) ps

      dotPatternInside = case tree of
        Leaf {}   -> False
        RecCon {} -> any ((== DotPat) . snd) ps

  if dotPatternInside then
    typeError $ NotSupported $
      "Dot patterns inside record patterns, " ++
      "unless accompanied by data type patterns"
   else
    return $ case tree of
      Leaf p     -> (p,   s, [Left p])
      RecCon t _ -> (pat, s, [Right (count, "r", t)])

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

translatePattern :: Pattern -> RecPatM (Pattern, Subst, Changes)
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
  [Arg Pattern] -> RecPatM ([Arg Pattern], Subst, Changes)
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
  RecPatM (Either (RecPatM (Pattern, Subst, Changes)) RecordTree)
recordTree p@(ConP _ Nothing _) = return $ Left $ translatePattern p
recordTree (ConP c (Just t) ps) = do
  rs <- mapM (recordTree . unArg) ps
  case allRight rs of
    Left rs ->
      return $ Left $ do
        (ps', ss, cs) <- unzip3 <$> mapM (either id removeTree) rs
        return (ConP c (Just t) (ps' `withArgsFrom` ps),
                concat ss, concat cs)
    Right ts -> do
      t <- reduce t
      case t of
        Arg { unArg = El _ (Def r args) } -> do
          rDef <- theDef <$> getConstInfo r
          case rDef of
            Record { recFields = fields } -> do
              let proj (_ , p) = \s t ->
                    Def p (substs s (map hide args) ++ [defaultArg t])
              return $ Right $ RecCon t $ zip (map proj fields) ts
            _ -> __IMPOSSIBLE__
        _ -> __IMPOSSIBLE__
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
  -> [(String, Arg Type)]
     -- ^ Old telescope, flattened, in textual left-to-right
     -- order.
  -> [Maybe (String, Arg Type)]
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
translateBody (Left _ : rest) s (NoBind b) = NoBind $ translateBody rest s b
translateBody []              s (Body t)   = Body $ substs s t
translateBody _               _ _          = __IMPOSSIBLE__

------------------------------------------------------------------------
-- Helper functions

-- | Turns a permutation into a substitution.

permToSubst :: Permutation -> Substitution
permToSubst (Perm n is) =
  [ makeVar i | i <- [0..n-1] ] ++ [ Var i [] | i <- [size is..] ]
  where
  makeVar i = case genericElemIndex i is of
    Nothing -> __IMPOSSIBLE__
    Just k  -> Var k []

-- | @dropBinds n b@ drops the initial @n@ occurrences of 'Bind' or
-- 'NoBind' from @b@.
--
-- Precondition: @b@ has to start with @n@ occurrences of 'Bind' or
-- 'NoBind'.

dropBinds :: Nat -> ClauseBody -> ClauseBody
dropBinds n b          | n == 0 = b
dropBinds n (Bind b)   | n > 0  = dropBinds (pred n) (absBody b)
dropBinds n (NoBind b) | n > 0  = dropBinds (pred n) b
dropBinds _ _                   = __IMPOSSIBLE__
