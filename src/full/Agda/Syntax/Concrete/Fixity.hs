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
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Concrete
import Agda.Syntax.Builtin (builtinsNoDef)
import Agda.TypeChecking.Positivity.Occurrence (Occurrence)

import Agda.Utils.Functor
import Agda.Utils.Null
import Agda.Utils.Impossible


type Fixities   = Map Name Fixity'
type Polarities = Map Name [Occurrence]

class Monad m => MonadFixityError m where
  throwMultipleFixityDecls            :: [(Name, [Fixity'])] -> m a
  throwMultiplePolarityPragmas        :: [Name] -> m a
  warnUnknownNamesInFixityDecl        :: [Name] -> m ()
  warnUnknownNamesInPolarityPragmas   :: [Name] -> m ()
  warnUnknownFixityInMixfixDecl       :: [Name] -> m ()
  warnPolarityPragmasButNotPostulates :: [Name] -> m ()

-- | Add more fixities. Throw an exception for multiple fixity declarations.
--   OR:  Disjoint union of fixity maps.  Throws exception if not disjoint.

plusFixities :: MonadFixityError m => Fixities -> Fixities -> m Fixities
plusFixities m1 m2
    -- If maps are not disjoint, report conflicts as exception.
    | not (null isect) = throwMultipleFixityDecls isect
    -- Otherwise, do the union.
    | otherwise        = return $ Map.unionWithKey mergeFixites m1 m2
  where
    --  Merge two fixities, assuming there is no conflict
    mergeFixites name (Fixity' f1 s1 r1) (Fixity' f2 s2 r2) = Fixity' f s $ fuseRange r1 r2
              where f | f1 == noFixity = f2
                      | f2 == noFixity = f1
                      | otherwise = __IMPOSSIBLE__
                    s | s1 == noNotation = s2
                      | s2 == noNotation = s1
                      | otherwise = __IMPOSSIBLE__

    -- Compute a list of conflicts in a format suitable for error reporting.
    isect = [ (x, map (Map.findWithDefault __IMPOSSIBLE__ x) [m1,m2])
            | (x, False) <- Map.assocs $ Map.intersectionWith compatible m1 m2 ]

    -- Check for no conflict.
    compatible (Fixity' f1 s1 _) (Fixity' f2 s2 _) =
      (f1 == noFixity   || f2 == noFixity  ) &&
      (s1 == noNotation || s2 == noNotation)

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
    mergePolarities p1 p2
      | Set.null i = return (Map.union p1 p2)
      | otherwise  = throwMultiplePolarityPragmas (Set.toList i)
      where
      i = Set.intersection (Map.keysSet p1) (Map.keysSet p2)

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
  fixs <- ifNull (Map.keysSet fixs Set.\\ declared) (return fixs) $ \ unknownFixs -> do
    when (doWarn == DoWarn) $ warnUnknownNamesInFixityDecl $ Set.toList unknownFixs
    -- Note: Data.Map.restrictKeys requires containers >= 0.5.8.2
    -- return $ Map.restrictKeys fixs declared
    return $ Map.filterWithKey (\ k _ -> Set.member k declared) fixs

  -- Same for undefined names in polarity declarations.
  pols <- ifNull (Map.keysSet pols Set.\\ declared) (return pols) $
    \ unknownPols -> do
      when (doWarn == DoWarn) $ warnUnknownNamesInPolarityPragmas $ Set.toList unknownPols
      -- Note: Data.Map.restrictKeys requires containers >= 0.5.8.2
      -- return $ Map.restrictKeys polarities declared
      return $ Map.filterWithKey (\ k _ -> Set.member k declared) pols

  -- If we have public mixfix identifiers without a corresponding fixity
  -- declaration, we raise a warning
  ifNull (Set.filter isOpenMixfix publicNames Set.\\ Map.keysSet fixs) (return ()) $
    when (doWarn == DoWarn) . warnUnknownFixityInMixfixDecl . Set.toList

  -- Check that every polarity pragma is used for a postulate.
  ifNull (Map.keysSet pols Set.\\ postulates) (return ()) $
    when (doWarn == DoWarn) . warnPolarityPragmasButNotPostulates . Set.toList

  return (fixs, pols)

fixitiesAndPolarities' :: MonadFixityError m => [Declaration] -> MonadicFixPol m
fixitiesAndPolarities' = foldMap $ \ d -> case d of
  -- These declarations define polarities:
  Pragma (PolarityPragma _ x occs) -> returnPol $ Map.singleton x occs
  -- These declarations define fixities:
  Syntax x syn    -> returnFix $ Map.singleton x (Fixity' noFixity syn $ getRange x)
  Infix  f xs     -> returnFix $ Map.fromList $ for xs $ \ x -> (x, Fixity' f noNotation $ getRange x)
  -- We look into these blocks:
  Mutual    _ ds' -> fixitiesAndPolarities' ds'
  Abstract  _ ds' -> fixitiesAndPolarities' ds'
  Private _ _ ds' -> fixitiesAndPolarities' ds'
  InstanceB _ ds' -> fixitiesAndPolarities' ds'
  Macro     _ ds' -> fixitiesAndPolarities' ds'
  -- All other declarations are ignored.
  -- We expand these boring cases to trigger a revisit
  -- in case the @Declaration@ type is extended in the future.
  TypeSig     {}  -> mempty
  Generalize  {}  -> mempty
  Field       {}  -> mempty
  FunClause   {}  -> mempty
  DataSig     {}  -> mempty
  DataDef     {}  -> mempty
  Data        {}  -> mempty
  RecordSig   {}  -> mempty
  RecordDef   {}  -> mempty
  Record      {}  -> mempty
  PatternSyn  {}  -> mempty
  Postulate   {}  -> mempty
  Primitive   {}  -> mempty
  Open        {}  -> mempty
  Import      {}  -> mempty
  ModuleMacro {}  -> mempty
  Module      {}  -> mempty
  UnquoteDecl {}  -> mempty
  UnquoteDef  {}  -> mempty
  Pragma      {}  -> mempty

data DeclaredNames = DeclaredNames { allNames, postulates, privateNames :: Set Name }

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
declaredNames d = case d of
  TypeSig _ x _        -> declaresName x
  Field _ x _          -> declaresName x
  FunClause (LHS p [] []) _ _ _
    | IdentP (QName x) <- removeSingletonRawAppP p
                       -> declaresName x
  FunClause{}          -> mempty
  DataSig _ _ x _ _    -> declaresName x
  DataDef _ _ _ _ cs   -> foldMap declaredNames cs
  Data _ _ x _ _ cs    -> declaresName x <> foldMap declaredNames cs
  RecordSig _ x _ _    -> declaresName x
  RecordDef _ x _ _ c _ _ -> declaresNames $     foldMap (:[]) (fst <$> c)
  Record _ x _ _ c _ _ _  -> declaresNames $ x : foldMap (:[]) (fst <$> c)
  Infix _ _            -> mempty
  Syntax _ _           -> mempty
  PatternSyn _ x _ _   -> declaresName x
  Mutual    _ ds       -> foldMap declaredNames ds
  Abstract  _ ds       -> foldMap declaredNames ds
  Private _ _ ds       -> allPrivateNames $ foldMap declaredNames ds
  InstanceB _ ds       -> foldMap declaredNames ds
  Macro     _ ds       -> foldMap declaredNames ds
  Postulate _ ds       -> allPostulates $ foldMap declaredNames ds
  Primitive _ ds       -> foldMap declaredNames ds
  Generalize _ ds      -> foldMap declaredNames ds
  Open{}               -> mempty
  Import{}             -> mempty
  ModuleMacro{}        -> mempty
  Module{}             -> mempty
  UnquoteDecl _ xs _   -> declaresNames xs
  UnquoteDef{}         -> mempty
  -- BUILTIN pragmas which do not require an accompanying definition declare
  -- the (unqualified) name they mention.
  Pragma (BuiltinPragma _ b (QName x))
    | b `elem` builtinsNoDef -> declaresName x
  Pragma{}             -> mempty

