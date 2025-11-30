-- | Warn about unused imports.
--
-- For each @open@ statement, we want to issue a warning about concrete names
-- brought into scope by this statement which are not referenced subsequently.
--
-- To this end, whenever we lookup a concrete name during scope checking,
-- we mark it as used by calling 'lookedupName' with the results of the lookup,
-- which is an 'AbstractName' or several 'AbstractName's in case the name
-- is ambiguous (e.g. an ambiguous constructor or projection).
--
-- We also record for each opened module the set of 'AbstractName's it brought
-- into scope.
--
-- When checking the file is done, we can traverse the each opened module
-- and report all the 'AbstractName's that we not used.

module Agda.Syntax.Scope.UnusedImports where

import Prelude hiding (null)

import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Syntax.Abstract.Name qualified as A
import Agda.Syntax.Common ( IsInstanceDef(isInstanceDef) )
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Position ( HasRange(getRange) )
import Agda.Syntax.Position qualified as P
import Agda.Syntax.Scope.Base as A

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Warnings (warning)

import Agda.Utils.Lens
import Agda.Utils.List1 ( pattern (:|), List1 )
import Agda.Utils.List1 qualified as List1
import Agda.Utils.List2 ( List2(..) )
import Agda.Utils.List2 qualified as List2
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null

import Agda.Utils.Impossible

-- import Agda.Syntax.Scope.Monad (ScopeM) -- cyclic import
type ScopeM = TCM -- to avoid cyclic imports

-- | Call these whenever a concrete name was translated to an abstract one.
lookedupName :: C.QName -> ResolvedName -> ScopeM ()
lookedupName x = \case
    DefinedName _access y _suffix -> unamb y
    FieldName ys                  -> add ys
    ConstructorName _ind ys       -> add ys
    PatternSynResName ys          -> add ys
    VarName{}                     -> return ()
    UnknownName{}                 -> return ()
  where
    add = \case
      y  :| []      -> unamb y
      y1 :| y2 : ys -> amb $ List2 y1 y2 ys
    unamb = modifyTCLens stUnambiguousLookups . Set.insert . A.anameName
    amb = modifyTCLens stAmbiguousLookups . IntMap.insert i . fmap A.anameName
    -- The range
    i = maybe __IMPOSSIBLE__ (fromIntegral . P.posPos) $ P.rStart' $ getRange x

-- lookedupName :: C.QName -> List1 AbstractName -> ScopeM ()
-- lookedupName x = \case
--   y :| [] -> modifyTCLens stUnambiguousLookups $ Set.insert y
--   y1 :| y2 :| ys -> modifyLens stAmbiguousLookups $ IntMap.insert i $ List2 y1 y2 ys
--   where
--     i = maybe __IMPOSSIBLE__ (fromIntegral . P.posPos) $ P.rStart' $ getRange x

-- | Call this when opening a module with all the names it brings into scope.
openedModule :: Scope -> ScopeM ()
openedModule (Scope m _parents ns imports _dataOrRec) = do
  -- imports have been removed by restrictPrivate
  unless (null imports) __IMPOSSIBLE__
  let
    broughtIntoScope :: NamesInScope -- [Map C.Name (List1 AbstractName)]
    broughtIntoScope = mergeNamesMany $ map (nsNames . snd) ns
  modifyTCLens stOpenedModules $ Map.insert m broughtIntoScope

-- openedModule :: ModuleName -> Set AbstractName -> ScopeM ()
-- openedModule m ys = modifyTCLens stOpenedModules $ Map.insert m ys

-- | Call this when a file has been checked.
warnUnusedImports :: ScopeM ()
warnUnusedImports = do
  st <- useTC stUnusedImportsState
  disambiguatedNames <- useTC stDisambiguatedNames
  let
    xs :: [A.QName]
    xs = flip concatMap (IntMap.toList $ ambiguousLookups st) \ (i :: Int, ys :: List2 A.QName) -> do
      case IntMap.lookup i disambiguatedNames of
        Just (DisambiguatedName _k x) -> [x]
        Nothing -> List2.toList ys -- __IMPOSSIBLE__

  -- Compute unambiguous lookups by using name disambiguation info from type checker.
  let lookups = unambiguousLookups st `Set.union` Set.fromList xs
  let
    isUsed :: A.AbstractName -> Bool
    isUsed y = isJust (isInstanceDef y) || anameName y `Set.member`lookups
  -- TODO: traverseWithKey_
  forM_ (Map.toList $ openedModules st) \ (m :: A.ModuleName, sc :: NamesInScope) -> do
    let
      unused :: [(C.Name, List1 A.AbstractName)]
      unused = filter (\ (_x :: C.Name, ys :: List1 A.AbstractName) -> all (not . isUsed) ys) $ Map.toList sc
    List1.unlessNull (map fst unused) \ unused1 -> do
      warning $ UnusedImports m unused1
  -- forMM_ (Map.toList <$> useTCLens stOpenedModules) \ (m, ys) -> do
  --   unused = filter (\ x -> anameName x `Set.notMember` lookups) $ Set.toList ys
  --   let unused = Map.restrictKeysSet ys lookups
  --   warning $ UnusedImports m unused

stUnambiguousLookups :: Lens' TCState (Set A.QName)
stUnambiguousLookups = stUnusedImportsState . lensUnambiguousLookups

stAmbiguousLookups :: Lens' TCState (IntMap (List2 A.QName))
stAmbiguousLookups = stUnusedImportsState . lensAmbiguousLookups

stOpenedModules :: Lens' TCState (Map A.ModuleName NamesInScope)
stOpenedModules = stUnusedImportsState . lensOpenedModules
