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

import Prelude hiding (null, (||))

import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.List (partition)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Interaction.Options (lensOptWarningMode, optQualifiedInstances)
import Agda.Interaction.Options.Warnings (lensSingleWarning, WarningName (UnusedImports_))

import Agda.Syntax.Abstract.Name qualified as A
import Agda.Syntax.Common ( IsInstanceDef(isInstanceDef) )
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Position ( HasRange(getRange), SetRange(setRange) )
import Agda.Syntax.Position qualified as P
import Agda.Syntax.Scope.Base as A

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Trace (setCurrentRange)
import Agda.TypeChecking.Warnings (warning)

import Agda.Utils.Boolean ( (||) )
import Agda.Utils.Lens
import Agda.Utils.List1 ( pattern (:|), List1 )
import Agda.Utils.List1 qualified as List1
import Agda.Utils.List2 ( List2(..) )
import Agda.Utils.List2 qualified as List2
import Agda.Utils.Map qualified as Map
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

-- | Call this when opening a module with all the names it brings into scope.
openedModule :: C.QName -> Scope -> ScopeM ()
openedModule x (Scope m0 _parents ns imports _dataOrRec) = do
  -- @imports@ have been removed by 'restrictPrivate'.
  unless (null imports) __IMPOSSIBLE__

  -- When the UnusedImports warning is off, do not collect information about @open@.
  -- E.g. we do not want to see warnings for the automatically inserted
  -- @open import Agda.Primitive using (Set)@.
  doWarn :: Bool <- useTC $ stPragmaOptions . lensOptWarningMode . lensSingleWarning UnusedImports_
  -- curM <- asksTC envCurrentModule
  reportSLn "warning.unusedImports" 20 $ unlines
    [ "openedModule: " <> prettyShow doWarn
    -- , "currentModule: " <> prettyShow curM
    ]
  when doWarn do
    let
      m = setRange (getRange x) m0
      broughtIntoScope :: NamesInScope -- [Map C.Name (List1 AbstractName)]
      broughtIntoScope = mergeNamesMany $ map (nsNames . snd) ns
    modifyTCLens stOpenedModules $ Map.insert m broughtIntoScope

-- | Call this when a file has been checked.
warnUnusedImports :: TCM ()
warnUnusedImports = do
    st <- useTC stUnusedImportsState
    disambiguatedNames <- useTC stDisambiguatedNames
    -- If instances can be used qualified, they do not need to be imported,
    -- so we should warn about them.
    qualifiedInstances <- optQualifiedInstances <$> pragmaOptions

    let
      xs :: [A.QName]
      xs = flip IntMap.foldMapWithKey (ambiguousLookups st) \ (i :: Int) (ys :: List2 A.QName) -> do
        case IntMap.lookup i disambiguatedNames of
          Just (DisambiguatedName _k x) -> [x]
          Nothing -> List2.toList ys -- __IMPOSSIBLE__

    -- Compute unambiguous lookups by using name disambiguation info from type checker.
    let
      lookups = unambiguousLookups st `Set.union` Set.fromList xs
      isLookedUp :: A.AbstractName -> Bool
      isLookedUp y = anameName y `Set.member`lookups
      isInst :: A.AbstractName -> Bool
      isInst = isJust . isInstanceDef
      isUsed :: A.AbstractName -> Bool
      isUsed = if qualifiedInstances then isLookedUp else isInst || isLookedUp
    -- For Andras: use 'forWithKey_' instead of @forM_ . Map.toList@.
    Map.forWithKey_ (openedModules st) \ (m :: A.ModuleName) (sc :: NamesInScope) -> do
      let
        warn = setCurrentRange m . warning . UnusedImports m
        used, unused :: [(C.Name, List1 A.AbstractName)]
        (used, unused) = partition (\ (_x :: C.Name, ys :: List1 A.AbstractName) -> any isUsed ys) $ Map.toList sc
      if null used then warn Nothing else
        List1.unlessNull (map snd unused) \ unused1 -> do
          warn $ Just $ fmap List1.head unused1

stUnambiguousLookups :: Lens' TCState (Set A.QName)
stUnambiguousLookups = stUnusedImportsState . lensUnambiguousLookups

stAmbiguousLookups :: Lens' TCState (IntMap (List2 A.QName))
stAmbiguousLookups = stUnusedImportsState . lensAmbiguousLookups

stOpenedModules :: Lens' TCState (Map A.ModuleName NamesInScope)
stOpenedModules = stUnusedImportsState . lensOpenedModules
