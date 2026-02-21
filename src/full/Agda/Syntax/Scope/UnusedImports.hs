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

module Agda.Syntax.Scope.UnusedImports
  ( lookedupName
  , registerModuleOpening
  , warnUnusedImports
  ) where

import Prelude hiding (null, (||))

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (partition)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Interaction.Options (lensOptWarningMode, optQualifiedInstances)
import Agda.Interaction.Options.Warnings (lensSingleWarning, WarningName (UnusedImports_, UnusedImportsAll_), warningSet, unusedImportsWarnings)

import Agda.Syntax.Abstract.Name
    ( WhyInScope(Defined, Opened, Applied),
      AbstractName(AbsName), anameName, anameLineage )
import Agda.Syntax.Abstract.Name qualified as A
import Agda.Syntax.Common ( IsInstanceDef(isInstanceDef), IsInstance, KwRange, ImportDirective' (using, impRenaming, publicOpen) )
import Agda.Syntax.Common.Pretty (prettyShow, Pretty (pretty))
import Agda.Syntax.Concrete qualified as C
import Agda.Syntax.Position ( HasRange(getRange), SetRange(setRange), Range )
import Agda.Syntax.Position qualified as P
import Agda.Syntax.Scope.Base as A
import Agda.Syntax.Scope.State ( ScopeM, withCurrentModule )
-- importing Agda.Syntax.Scope.Monad creates import cycles

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug ( reportSLn, __IMPOSSIBLE_VERBOSE__ )
import Agda.TypeChecking.Monad.Trace (setCurrentRange)
import Agda.TypeChecking.Warnings (warning)

import Agda.Utils.Boolean  ( (||) )
import Agda.Utils.Function ( applyUnless )
import Agda.Utils.Lens     ( (<&>), Lens' )
import Agda.Utils.List     ( partitionMaybe, hasElem )
import Agda.Utils.List1    ( pattern (:|), List1 )
import Agda.Utils.List1    qualified as List1
import Agda.Utils.List2    ( List2(..) )
import Agda.Utils.List2    qualified as List2
import Agda.Utils.Map      qualified as Map
import Agda.Utils.Maybe    ( fromMaybe, isJust, whenNothing )
import Agda.Utils.Monad    ( forM_, when, unless )
import Agda.Utils.Null     ( Null(null) )

import Agda.Utils.Impossible

-- | Call these whenever a concrete name was translated to an abstract one.
lookedupName ::
     C.QName       -- ^ The concrete name resolved by the scope checker.
  -> ResolvedName  -- ^ The resolution of the name.
  -> ScopeM ()
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
    unamb = modifyTCLens stUnambiguousLookups . (:)
    amb xs = case rangeToPosPos x of
      -- Andreas, 2025-11-30
      -- It can happen that a concrete identifier has no range,
      -- e.g. when it comes from an expanded ellipsis.
      -- In this case, we do not record the lookup,
      -- since it should have been looked up already
      -- when processing the pattern from the original lhs
      -- (that was duplicated by ellipsis expansion).
      -- See test/interaction/ExpandEllipsis.
      Nothing -> pure ()
      Just i -> modifyTCLens stAmbiguousLookups $ IntMap.insert i xs

rangeToPosPos :: HasRange a => a -> Maybe Int
rangeToPosPos = fmap (fromIntegral . P.posPos) . P.rStart' . getRange

-- | Call this when opening a module with all the names it brings into scope.
--   When the 'UnusedImports' warning is enabled, we will store this information
--   to later issue a warning connected to this 'open' statement
--   for the names that were not used.
registerModuleOpening ::
     KwRange             -- ^ Range of the @open@ keyword.
  -> A.ModuleName        -- ^ Parent module: module into which we pour the opened module.
  -> C.QName             -- ^ Opened module.
  -> C.ImportDirective   -- ^ Directive restricting the scope of the opened module.
  -> Scope               -- ^ The scope resulting from applying the import directive.
  -> ScopeM ()
registerModuleOpening kwr currentModule x dir (Scope m0 _parents ns imports _dataOrRec) = do
  -- @imports@ have been removed by 'restrictPrivate'.
  unless (null imports) __IMPOSSIBLE__

  -- When the UnusedImports warning is off, do not collect information about @open@.
  -- E.g. we do not want to see warnings for the automatically inserted
  -- @open import Agda.Primitive using (Set)@.
  -- It is sufficient to check for 'UnusedImports_' since it is implied by 'UnusedImportsAll_'.
  doWarn <- (UnusedImports_ `Set.member`) <$> useTC stWarningSet
  reportSLn "warning.unusedImports" 20 $ unlines
    [ "openedModule: " <> prettyShow doWarn
    , "x = " <> prettyShow x
    -- , "currentModule: " <> prettyShow curM
    ]
  when doWarn $ whenNothing (publicOpen dir) do
    let
      m = setRange (getRange x) m0
      broughtIntoScope :: NamesInScope -- [Map C.Name (List1 AbstractName)]
      broughtIntoScope = mergeNamesMany $ map (nsNames . snd) ns
      !k = fromMaybe __IMPOSSIBLE__ $ rangeToPosPos x
      hasDir = not (null (using dir)) || not (null (impRenaming dir))
    modifyTCLens stOpenedModules $
      IntMap.insert k (OpenedModule kwr m currentModule hasDir broughtIntoScope)

-- | Call this when a file has been checked to generate the unused-imports warnings for each opened module.
--   Assumes that all names have been looked up via 'lookedupName'.
--   Needs the disambiguation information from the type checker to correctly report ununsed overloaded names.
warnUnusedImports :: TCM ()
warnUnusedImports = do
    warnAll <- (UnusedImportsAll_ `Set.member`) <$> useTC stWarningSet
    st <- useTC stUnusedImportsState
    disambiguatedNames <- useTC stDisambiguatedNames
    -- If instances can be used qualified, they do not need to be imported,
    -- so we should warn about them.
    qualifiedInstances <- optQualifiedInstances <$> pragmaOptions

    reportSLn "warning.unusedImports" 60 $ "unambiguousLookups: " <> prettyShow (unambiguousLookups st)

    let
      -- Disambiguate overloaded lookups.
      addAmbLookup (i :: Int) (ys :: List2 AbstractName) = do
        case IntMap.lookup i disambiguatedNames of
          Just (DisambiguatedName _k x) -> (filter ((x ==) . anameName) (List2.toList ys) ++)
          Nothing -> (List2.toList ys ++) -- __IMPOSSIBLE__
      allLookups :: [AbstractName]
      allLookups = IntMap.foldrWithKey addAmbLookup (unambiguousLookups st) (ambiguousLookups st)

      -- To make a set of the list of looked-up 'AbstractName's,
      -- we need to convert them to 'ImportedName's lest we
      -- conflate names from different openings.
      lookups :: [ImportedName]
      (unknowns, lookups) = partitionMaybe toImportedName allLookups
      isLookedUp, isInst, isUsed  :: ImportedName -> Bool
      isLookedUp = hasElem lookups
      isInst = isJust . isInstanceDef
      isUsed = applyUnless qualifiedInstances (isInst ||) isLookedUp

    reportSLn "warning.unusedImports" 60 $ "allLookups: " <> prettyShow allLookups
    reportSLn "warning.unusedImports" 60 $ "lookups: " <> prettyShow lookups
    reportSLn "warning.unusedImports" 60 $ "unknowns: " <> prettyShow unknowns

    -- Iterate through the @open@ statements and issue warnings.
    forM_ (openedModules st) \ (OpenedModule (kwr :: KwRange) (m :: A.ModuleName) (parent :: A.ModuleName) (hasDir :: Bool) (sc :: NamesInScope)) -> do
      let
        -- Partition the names brought into scope by the open statement
        -- into used and unused ones.
        f :: (C.Name, List1 AbstractName) -> Maybe (C.Name, List1 ImportedName)
        f = traverse $ traverse toImportedName
        -- f (x, ys) = (x ,) <$> traverse toImportedName ys
        imps, imps', used, unused :: [(C.Name, List1 ImportedName)]
        (other, imps) = partitionMaybe f $ Map.toList sc
        imps' = map (\ (x, ys) -> (x, setRange (getRange x) <$> ys)) imps
        (used, unused) = partition (any isUsed . snd) imps'

      reportSLn "warning.unusedImports" 60 $ "used: " <> prettyShow used
      reportSLn "warning.unusedImports" 60 $ "unused: " <> prettyShow unused
      unless (null other) $ __IMPOSSIBLE_VERBOSE__ (show other)

      let
        -- Commands to issue the warnings:
        warn = setCurrentRange (getRange (kwr, m)) . withCurrentModule parent . warning . UnusedImports m
        warnModule = warn Nothing
        warnEach = do
          List1.unlessNull (map snd unused) \ unused1 -> do
            warn $ Just $ fmap (iName . List1.head) unused1

      -- Issue warning.
      -- If nothing was used, we warn about the whole import.
      -- If the open statement has a 'using' or 'renaming' directive,
      -- or if the 'UnusedImportsAll_' warning is enabled,
      -- we warn about each unused name individually.
      -- Otherwise, we just warn once about the whole import.
      if  | hasDir      -> warnEach
          | null used   -> warnModule
          | warnAll     -> warnEach
          | otherwise   -> pure ()

------------------------------------------------------------------------------
-- * Auxiliary definitions

-- | A wrapper around 'AbstractName' to make the position of the 'Opened' in the lineage available.
--   This wrapper is needed when 'AbstractName's are stored in sets
--   so that we do not conflate different 'AbstractName's with the same underlying 'A.QName'
--   that were brought into scope by different 'open' statements.
data ImportedName = ImportedName
  { iWhere :: Int -- Position of 'Opened' extracted from the 'AbstractName'.
  , iName  :: AbstractName
  } deriving (Eq, Ord, Show)

instance HasRange ImportedName where
  getRange = getRange . iName

instance SetRange ImportedName where
  setRange r (ImportedName i n) = ImportedName i (setRange r n)

instance Pretty ImportedName where
  pretty (ImportedName i n) = pretty n <> " (at position " <> pretty i <> ")"

instance IsInstanceDef ImportedName where
  isInstanceDef = isInstanceDef . iName

-- | Convert an 'AbstractName' to an 'ImportedName' if it was brought into scope by an 'open' statement.
toImportedName :: AbstractName -> Maybe ImportedName
toImportedName x = case anameLineage x of
  Opened m _ -> rangeToPosPos m <&> (`ImportedName` x)
  Applied{} -> Nothing
  Defined{} -> Nothing

-- Lenses for the components of the UnusedImportsState in the TCState.

stUnambiguousLookups :: Lens' TCState [AbstractName]
stUnambiguousLookups = stUnusedImportsState . lensUnambiguousLookups

stAmbiguousLookups :: Lens' TCState (IntMap (List2 AbstractName))
stAmbiguousLookups = stUnusedImportsState . lensAmbiguousLookups

stOpenedModules :: Lens' TCState (IntMap OpenedModule)
stOpenedModules = stUnusedImportsState . lensOpenedModules
