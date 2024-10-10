{-# OPTIONS_GHC -Wunused-imports #-}

-- | Collecting fixity declarations (and polarity pragmas) for concrete
--   declarations.

module Agda.Syntax.Concrete.Fixity
  ( Fixities, Polarities, MonadFixityError(..)
  , DoWarn(..)
  , fixitiesAndPolarities
  ) where

import Prelude hiding (null)

import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Builtin (builtinById, isBuiltinNoDef)
import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Position
import Agda.TypeChecking.Positivity.Occurrence (Occurrence)

import Agda.Utils.CallStack (HasCallStack)
import Agda.Utils.Functor
import Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Null
import Agda.Utils.Set1 (Set1)
import qualified Agda.Utils.Set1 as Set1
import Agda.Utils.Tuple (Pair(Pair))

import Agda.Utils.Impossible


type Fixities   = Map Name Fixity'
type Polarities = Map Name (List1 Occurrence)

class Monad m => MonadFixityError m where
  throwMultipleFixityDecls            :: List1 (Name, Pair Fixity') -> m a
  throwMultiplePolarityPragmas        :: List1 Name -> m a
  warnUnknownNamesInFixityDecl        :: HasCallStack => Set1 Name -> m ()
  warnUnknownNamesInPolarityPragmas   :: HasCallStack => Set1 Name -> m ()
  warnUnknownFixityInMixfixDecl       :: HasCallStack => Set1 Name -> m ()
  warnPolarityPragmasButNotPostulates :: HasCallStack => Set1 Name -> m ()
  warnEmptyPolarityPragma             :: HasCallStack => Range -> m ()

-- | Add more fixities. Throw an exception for multiple fixity declarations.
--   OR:  Disjoint union of fixity maps.  Throws exception if not disjoint.

plusFixities :: MonadFixityError m => Fixities -> Fixities -> m Fixities
plusFixities m1 m2
    -- If maps are not disjoint, report conflicts as exception.
    | Just ds <- List1.nonEmpty isect = throwMultipleFixityDecls ds
    -- Otherwise, do the union.
    | otherwise        = return $ Map.unionWithKey mergeFixites m1 m2
  where
    --  Merge two fixities, assuming there is no conflict
    mergeFixites name (Fixity' f1 s1 r1) (Fixity' f2 s2 r2) = Fixity' f s $ fuseRange r1 r2
              where f | null f1 = f2
                      | null f2 = f1
                      | otherwise = __IMPOSSIBLE__
                    s | null s1 = s2
                      | null s2 = s1
                      | otherwise = __IMPOSSIBLE__

    -- Compute a list of conflicts in a format suitable for error reporting.
    isect = [ (x, fmap (Map.findWithDefault __IMPOSSIBLE__ x) $ Pair m1 m2)
            | (x, False) <- Map.assocs $ Map.intersectionWith compatible m1 m2 ]

    -- Check for no conflict.
    compatible (Fixity' f1 s1 _) (Fixity' f2 s2 _) =
      (null f1 || null f2) &&
      (null s1 || null s2)

-- | While 'Fixities' and Polarities are not semigroups under disjoint
--   union (which might fail), we get a semigroup instance for the
--   monadic @m (Fixities, Polarities)@ which propagates the first
--   error.
newtype MonadicFixPol m = MonadicFixPol { runMonadicFixPol :: m (Fixities, Polarities) }

returnFix :: Monad m => Fixities -> MonadicFixPol m
returnFix fx = MonadicFixPol $ return (fx, Map.empty)

returnPol :: Monad m => Polarities -> MonadicFixPol m
returnPol pol = MonadicFixPol $ return (Map.empty, pol)

instance MonadFixityError m => Semigroup (MonadicFixPol m) where
  c1 <> c2 = MonadicFixPol $ do
    (f1, p1) <- runMonadicFixPol c1
    (f2, p2) <- runMonadicFixPol c2
    f <- plusFixities f1 f2
    p <- mergePolarities p1 p2
    return (f, p)
    where
    -- Merge disjoint maps.
    mergePolarities p1 p2 =
      List1.ifNull (Map.keys $ Map.intersection p1 p2)
        {-then-} (return $ Map.union p1 p2)
        {-else-} \ ks -> throwMultiplePolarityPragmas ks

instance MonadFixityError m => Monoid (MonadicFixPol m) where
  mempty  = MonadicFixPol $ return (Map.empty, Map.empty)
  mappend = (<>)

data DoWarn = NoWarn | DoWarn
  deriving (Eq, Show)

-- | Get the fixities and polarity pragmas from the current block.
--   Doesn't go inside modules and where blocks.
--   The reason for this is that these declarations have to appear at the same
--   level (or possibly outside an abstract or mutual block) as their target
--   declaration.
fixitiesAndPolarities :: MonadFixityError m => DoWarn -> [Declaration] -> m (Fixities, Polarities)
fixitiesAndPolarities doWarn ds = do
  (fixs, pols) <- runMonadicFixPol $ fixitiesAndPolarities' ds
  let DeclaredNames declared postulates privateNames = foldMap declaredNames ds
  let publicNames = declared Set.\\ privateNames

  -- If we have names in fixity declarations which are not defined in the
  -- appropriate scope, raise a warning and delete them from fixs.
  fixs <- Set1.ifNull (Map.keysSet fixs Set.\\ declared) (return fixs) $ \ unknownFixs -> do
    when (doWarn == DoWarn) $ warnUnknownNamesInFixityDecl unknownFixs
    -- Note: Data.Map.restrictKeys requires containers >= 0.5.8.2
    -- return $ Map.restrictKeys fixs declared
    return $ Map.filterWithKey (\ k _ -> Set.member k declared) fixs

  -- Same for undefined names in polarity declarations.
  pols <- Set1.ifNull (Map.keysSet pols Set.\\ declared) (return pols) $
    \ unknownPols -> do
      when (doWarn == DoWarn) $ warnUnknownNamesInPolarityPragmas unknownPols
      -- Note: Data.Map.restrictKeys requires containers >= 0.5.8.2
      -- return $ Map.restrictKeys polarities declared
      return $ Map.filterWithKey (\ k _ -> Set.member k declared) pols

  -- If we have public mixfix identifiers without a corresponding fixity
  -- declaration, we raise a warning
  Set1.unlessNull (Set.filter isOpenMixfix publicNames Set.\\ Map.keysSet fixs) $
    when (doWarn == DoWarn) . warnUnknownFixityInMixfixDecl

  -- Check that every polarity pragma is used for a postulate.
  Set1.unlessNull (Map.keysSet pols Set.\\ postulates) $
    when (doWarn == DoWarn) . warnPolarityPragmasButNotPostulates

  return (fixs, pols)

fixitiesAndPolarities' :: MonadFixityError m => [Declaration] -> MonadicFixPol m
fixitiesAndPolarities' = foldMap $ \case
  -- These declarations define polarities:
  Pragma (PolarityPragma r x occs) ->
    List1.ifNull occs (MonadicFixPol $ warnEmptyPolarityPragma r $> mempty) {-else-} \ occs ->
      returnPol $ Map.singleton x occs
  -- These declarations define fixities:
  Syntax x syn    -> returnFix $ Map.singleton x (Fixity' noFixity syn $ getRange x)
  Infix  f xs     -> returnFix $ Map.fromList $ for (List1.toList xs) $ \ x -> (x, Fixity' f noNotation $ getRange x)
  -- We look into these blocks:
  Mutual    _ ds' -> fixitiesAndPolarities' ds'
  InterleavedMutual _ ds' -> fixitiesAndPolarities' ds'
  Abstract  _ ds' -> fixitiesAndPolarities' ds'
  Private _ _ ds' -> fixitiesAndPolarities' ds'
  InstanceB _ ds' -> fixitiesAndPolarities' ds'
  Macro     _ ds' -> fixitiesAndPolarities' ds'
  Opaque    _ ds' -> fixitiesAndPolarities' ds'
  -- All other declarations are ignored.
  -- We expand these boring cases to trigger a revisit
  -- in case the @Declaration@ type is extended in the future.
  TypeSig         {}  -> mempty
  FieldSig        {}  -> mempty
  Generalize      {}  -> mempty
  Field           {}  -> mempty
  FunClause       {}  -> mempty
  DataSig         {}  -> mempty
  DataDef         {}  -> mempty
  Data            {}  -> mempty
  RecordSig       {}  -> mempty
  RecordDef       {}  -> mempty
  Record          {}  -> mempty
  LoneConstructor {}  -> mempty
  PatternSyn      {}  -> mempty
  Postulate       {}  -> mempty
  Primitive       {}  -> mempty
  Open            {}  -> mempty
  Import          {}  -> mempty
  ModuleMacro     {}  -> mempty
  Module          {}  -> mempty
  UnquoteDecl     {}  -> mempty
  UnquoteDef      {}  -> mempty
  UnquoteData     {}  -> mempty
  Pragma          {}  -> mempty
  Unfolding       {}  -> mempty

data DeclaredNames = DeclaredNames { _allNames, _postulates, _privateNames :: Set Name }

instance Semigroup DeclaredNames where
  DeclaredNames xs ps as <> DeclaredNames ys qs bs =
    DeclaredNames (xs <> ys) (ps <> qs) (as <> bs)

instance Monoid DeclaredNames where
  mempty  = DeclaredNames Set.empty Set.empty Set.empty
  mappend = (<>)

allPostulates :: DeclaredNames -> DeclaredNames
allPostulates (DeclaredNames xs ps as) = DeclaredNames xs (xs <> ps) as

allPrivateNames :: DeclaredNames -> DeclaredNames
allPrivateNames (DeclaredNames xs ps as) = DeclaredNames xs ps (xs <> as)

declaresNames :: [Name] -> DeclaredNames
declaresNames xs = DeclaredNames (Set.fromList xs) Set.empty Set.empty

declaresName :: Name -> DeclaredNames
declaresName x = declaresNames [x]

-- | Compute the names defined in a declaration. We stay in the current scope,
--   i.e., do not go into modules.
declaredNames :: Declaration -> DeclaredNames
declaredNames = \case
  TypeSig _ _ x _       -> declaresName x
  FieldSig _ _ x _      -> declaresName x
  Field _ fs            -> foldMap declaredNames fs
  FunClause (LHS p [] []) _ _ _
    | IdentP _ (QName x) <- removeParenP p
                        -> declaresName x
  FunClause{}           -> mempty
  DataSig _ _ x _ _     -> declaresName x
  DataDef _ _ _ cs      -> foldMap declaredNames cs
  Data _ _ x _ _ cs     -> declaresName x <> foldMap declaredNames cs
  RecordSig _ _ x _ _   -> declaresName x
  RecordDef _ x ds _ _  -> declaresNames $     maybeToList (recDirConstructor ds)
  Record _ _ x ds _ _ _ -> declaresNames $ x : maybeToList (recDirConstructor ds)
  Infix _ _             -> mempty
  Syntax _ _            -> mempty
  PatternSyn _ x _ _    -> declaresName x
  Mutual    _ ds        -> foldMap declaredNames ds
  InterleavedMutual    _ ds -> foldMap declaredNames ds
  LoneConstructor _ ds  -> foldMap declaredNames ds
  Abstract  _ ds        -> foldMap declaredNames ds
  Private _ _ ds        -> allPrivateNames $ foldMap declaredNames ds
  InstanceB _ ds        -> foldMap declaredNames ds
  Macro     _ ds        -> foldMap declaredNames ds
  Postulate _ ds        -> allPostulates $ foldMap declaredNames ds
  Primitive _ ds        -> foldMap declaredNames ds
  Generalize _ ds       -> foldMap declaredNames ds
  Opaque _ ds           -> foldMap declaredNames ds
  Open{}                -> mempty
  Unfolding{}           -> mempty
  Import{}              -> mempty
  ModuleMacro{}         -> mempty
  Module{}              -> mempty
  UnquoteDecl _ xs _    -> declaresNames xs
  UnquoteDef{}          -> mempty
  UnquoteData _ x cs _  -> declaresNames (x:cs)
  -- BUILTIN pragmas which do not require an accompanying definition declare
  -- the (unqualified) name they mention.
  Pragma (BuiltinPragma _ b (QName x))
    | any isBuiltinNoDef . builtinById $ rangedThing b -> declaresName x
  Pragma{}             -> mempty

recDirConstructor :: [RecordDirective] -> Maybe Name
recDirConstructor = listToMaybe . mapMaybe \case
  Constructor x _ -> Just x
  _ -> Nothing
