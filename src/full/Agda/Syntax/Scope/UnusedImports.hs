-- | Warn about unused imports.
--
-- For each @open@ statement, we want to issue a warning about concrete names
-- and modules brought into scope by this statement which are not referenced subsequently.
--
-- To this end, whenever we lookup a concrete name during scope checking,
-- we mark it as used by calling 'lookedupName' with the results of the lookup,
-- which is an 'AbstractName' or several 'AbstractName's in case the name
-- is ambiguous (e.g. an ambiguous constructor or projection).
-- Likewise, whenever we resolve a concrete module name,
-- we mark the resulting 'AbstractModule' as used by calling 'lookedupModule'.
-- If the concrete name is qualified, e.g. @M.x@,
-- we also mark the module @M@ as used that the qualifier resolved to.
--
-- We also record for each opened module the set of 'AbstractName's
-- and 'AbstractModule's it brought into scope.
--
-- When checking the file is done, we can traverse the each opened module
-- and report all the 'AbstractName's and 'AbstractModule's that we not used.

module Agda.Syntax.Scope.UnusedImports
  ( lookedupName
  , lookedupModule
  , registerModuleOpening
  , warnUnusedImports
  ) where

import Prelude hiding (null, (||))

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (partition, sortOn)
import Data.Map qualified as Map
import Data.Set qualified as Set

import Agda.Interaction.Options (optQualifiedInstances)
import Agda.Interaction.Options.Warnings (WarningName (UnusedImports_, UnusedImportsAll_))

import Agda.Syntax.Abstract.Name
    ( WhyInScope(Defined, Opened, Applied),
      AbstractName, anameName, anameLineage,
      AbstractModule, amodName, amodLineage )
import Agda.Syntax.Abstract.Name qualified as A
import Agda.Syntax.Common
  ( IsInstanceDef(isInstanceDef), KwRange
  , ImportDirective'(using, impRenaming, publicOpen)
  , ImportedName'(ImportedName, ImportedModule), fromImportedName, Renaming'(renTo), Using'(Using, UseEverything)
  )
import Agda.Syntax.Common.Pretty (prettyShow, Pretty (pretty))
import Agda.Syntax.Concrete qualified as C
import Agda.Syntax.Position ( HasRange(getRange), SetRange(setRange) )
import Agda.Syntax.Position qualified as P
import Agda.Syntax.Scope.Base as A
import Agda.Syntax.Scope.State ( ScopeM, withCurrentModule )
-- importing Agda.Syntax.Scope.Monad creates import cycles

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug ( MonadDebug, reportSLn, __IMPOSSIBLE_VERBOSE__ )
import Agda.TypeChecking.Monad.State ( getScope )
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
import Agda.Utils.Maybe    ( fromMaybe, isJust, mapMaybe, whenNothing )
import Agda.Utils.Monad    ( forM_, when, unless, whenM )
import Agda.Utils.Null     ( Null(null) )

import Agda.Utils.Impossible

-- | Call these whenever a concrete name was translated to an abstract one.
lookedupName ::
     C.QName       -- ^ The concrete name resolved by the scope checker.
  -> ResolvedName  -- ^ The resolution of the name.
  -> ScopeM ()
lookedupName x = \case
    DefinedName _access y _suffix -> unamb y >> lookedupQualifier x [y]
    FieldName ys                  -> add ys
    ConstructorName _ind ys       -> add ys
    PatternSynResName ys          -> add ys
    VarName{}                     -> return ()
    UnknownName{}                 -> return ()
  where
    add ys = do
      case ys of
        y  :| []      -> unamb y
        y1 :| y2 : ys -> amb $ List2 y1 y2 ys
      lookedupQualifier x $ List1.toList ys
    unamb = modifyTCLens stUnambiguousLookups . (:)
    amb xs = case rangeToPosPos x of
      -- Andreas, 2025-11-30
      -- It can happen that a concrete identifier has no range,
      -- e.g. when it comes from an expanded ellipsis.
      -- In this case, we do not record the lookup,
      -- since it should have been looked up already
      -- when processing the pattern from the original lhs
      -- (that was duplicated by ellipsis expansion).
      -- See test/Interaction/ExpandEllipsis.
      Nothing -> pure ()
      Just i -> modifyTCLens stAmbiguousLookups $ IntMap.insert i xs

-- | Call this whenever a concrete module name was translated to an abstract one.
lookedupModule ::
     C.QName         -- ^ The concrete module name resolved by the scope checker.
  -> AbstractModule  -- ^ The resolution of the module name.
  -> ScopeM ()
lookedupModule x m = do
  modifyTCLens stModuleLookups (m :)
  lookedupQualifier x [m]

-- | If the concrete name @x@ is qualified, i.e., of the form @M.y@,
--   mark the modules @M@ as used through which @x@ resolved to (one of) the given things.
lookedupQualifier :: InScope a => C.QName -> [a] -> ScopeM ()
lookedupQualifier x ys = case x of
  C.QName{} -> pure ()
  C.Qual{}  -> whenM unusedImportsEnabled do
    ms <- scopeLookupQualifier x ys <$> getScope
    modifyTCLens stModuleLookups (ms ++)

-- | Is the 'UnusedImports' warning on?
--   It is sufficient to check for 'UnusedImports_' since it is implied by 'UnusedImportsAll_'.
unusedImportsEnabled :: ScopeM Bool
unusedImportsEnabled = (UnusedImports_ `Set.member`) <$> useTC stWarningSet

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
  doWarn <- unusedImportsEnabled
  reportSLn "warning.unusedImports" 20 $ unlines
    [ "openedModule: " <> prettyShow doWarn
    , "x = " <> prettyShow x
    -- , "currentModule: " <> prettyShow curM
    ]
  when doWarn $ whenNothing (publicOpen dir) do
    let
      m = setRange (getRange x) m0
      names   :: NamesInScope   -- Map C.Name (List1 AbstractName)
      names   = mergeNamesMany $ map (nsNames . snd) ns
      modules :: ModulesInScope -- Map C.Name (List1 AbstractModule)
      modules = mergeNamesMany $ map (nsModules . snd) ns
      -- The modules mentioned in the directive.
      explicitModules = Set.fromList
        [ y | ImportedModule y <- usingList ++ map renTo (impRenaming dir) ]
      usingList = case using dir of
        UseEverything -> []
        Using ys      -> ys
      -- Modules that come with a name, e.g. modules of data and record types.
      -- We recognize them either by their abstract name,
      -- or by their concrete name (needed for copies made by module application,
      -- since these get fresh abstract names).
      companions = Map.keysSet (Map.filterWithKey isCompanion modules)
      isCompanion y zs = Set.notMember y explicitModules &&
        (Map.member y names || any ((`Set.member` nameModules) . amodName) zs)
      nameModules = Set.fromList $ map (A.qnameToMName . anameName) $ concatMap List1.toList $ Map.elems names
      !k = fromMaybe __IMPOSSIBLE__ $ rangeToPosPos x
      hasDir = not (null (using dir)) || not (null (impRenaming dir))
    modifyTCLens stOpenedModules $
      IntMap.insert k (OpenedModule kwr m currentModule hasDir names modules companions)

-- | Call this when a file has been checked to generate the unused-imports warnings for each opened module.
--   Assumes that all names have been looked up via 'lookedupName'
--   and all modules via 'lookedupModule'.
--   Needs the disambiguation information from the type checker to correctly report ununsed overloaded names.
warnUnusedImports :: TCM ()
warnUnusedImports = do
    warnAll <- (UnusedImportsAll_ `Set.member`) <$> useTC stWarningSet
    st <- useTC stUnusedImportsState
    disambiguatedNames <- useTC stDisambiguatedNames
    -- If instances can be used qualified, they do not need to be imported,
    -- so we should warn about them.
    qualifiedInstances <- optQualifiedInstances <$> pragmaOptions

    reportSLn "warning.unusedImports" 60 $ "ambiguousLookups: " <> prettyShow (ambiguousLookups st)
    reportSLn "warning.unusedImports" 60 $ "unambiguousLookups: " <> prettyShow (unambiguousLookups st)
    reportSLn "warning.unusedImports" 60 $ "moduleLookups: " <> prettyShow (moduleLookups st)

    let
      -- Disambiguate overloaded lookups.
      addAmbLookup (i :: Int) (ys :: List2 AbstractName) = do
        case IntMap.lookup i disambiguatedNames of
          Just (DisambiguatedName _k x) -> (filter ((x ==) . anameName) (List2.toList ys) ++)
          Nothing -> (List2.toList ys ++) -- __IMPOSSIBLE__
      allLookups :: [AbstractName]
      allLookups = IntMap.foldrWithKey addAmbLookup (unambiguousLookups st) (ambiguousLookups st)

      -- To make a set of the list of looked-up 'AbstractName's,
      -- we need to convert them to 'Imported' lest we
      -- conflate names from different openings.
      -- Same for the 'AbstractModule's.
      lookups :: [Imported AbstractName]
      (unknowns, lookups) = partitionMaybe toImported allLookups
      moduleLookups' :: [Imported AbstractModule]
      moduleLookups' = mapMaybe toImported $ moduleLookups st

      isInst, isUsedName :: Imported AbstractName -> Bool
      isInst = isJust . isInstanceDef . iThing
      isUsedName = applyUnless qualifiedInstances (isInst ||) $ hasElem lookups
      isUsedModule :: Imported AbstractModule -> Bool
      isUsedModule = hasElem moduleLookups'

    reportSLn "warning.unusedImports" 60 $ "allLookups: " <> prettyShow allLookups
    reportSLn "warning.unusedImports" 60 $ "lookups: " <> prettyShow lookups
    reportSLn "warning.unusedImports" 60 $ "unknowns: " <> prettyShow unknowns

    -- Iterate through the @open@ statements and issue warnings.
    forM_ (openedModules st) \ (OpenedModule kwr m parent hasDir names modules companions) -> do

      -- Partition the names and modules brought into scope by the open statement
      -- into used and unused ones.
      (usedNames, unusedNames) <- partitionUsed isUsedName names
      (usedModules, unusedModules) <- partitionUsed isUsedModule modules

      let
        used = not (null usedNames && null usedModules)
        -- Unused things to report individually, in alphabetical order.
        -- We omit the modules of data and record types not mentioned explicitly,
        -- since we report their names already.
        unused :: [C.ImportedName]
        unused = sortOn fromImportedName $ concat
          [ map ImportedName unusedNames
          , map ImportedModule $ filter (`Set.notMember` companions) unusedModules
          ]

        -- Commands to issue the warnings:
        warn = setCurrentRange (getRange (kwr, m)) . withCurrentModule parent . warning . UnusedImports m
        warnModule = warn Nothing
        warnEach = List1.unlessNull unused $ warn . Just

      -- Issue warning.
      -- If nothing was used, we warn about the whole import.
      -- If the open statement has a 'using' or 'renaming' directive,
      -- or if the 'UnusedImportsAll_' warning is enabled,
      -- we warn about each unused name individually.
      -- Otherwise, we just warn once about the whole import.
      if  | hasDir      -> warnEach
          | not used    -> warnModule
          | warnAll     -> warnEach
          | otherwise   -> pure ()

-- | Partition the things brought into scope by an @open@ statement
--   into the used and unused ones.
--   Returns the concrete names they are in scope under.
partitionUsed :: forall a m. (Lineage a, MonadDebug m)
  => (Imported a -> Bool)  -- ^ Was the thing used?
  -> ThingsInScope a       -- ^ The things brought into scope by the @open@.
  -> m ([C.Name], [C.Name])
partitionUsed isUsed sc = do
  let
    imps, used, unused :: [(C.Name, List1 (Imported a))]
    (other, imps) = partitionMaybe (traverse $ traverse toImported) $ Map.toList sc
    (used, unused) = partition (any isUsed . snd) imps
  reportSLn "warning.unusedImports" 60 $ "used: " <> prettyShow used
  reportSLn "warning.unusedImports" 60 $ "unused: " <> prettyShow unused
  unless (null other) $ __IMPOSSIBLE_VERBOSE__ (show other)
  return (map fst used, map fst unused)

------------------------------------------------------------------------------
-- * Auxiliary definitions

-- | Things (names and modules) that remember how they came into scope.
class (Ord a, Show a, Pretty a) => Lineage a where
  lineage :: a -> WhyInScope

instance Lineage AbstractName where
  lineage = anameLineage

instance Lineage AbstractModule where
  lineage = amodLineage

-- | A wrapper around 'AbstractName' or 'AbstractModule'
--   to make the position of the 'Opened' in the lineage available.
--   This wrapper is needed when 'AbstractName's are stored in sets
--   so that we do not conflate different 'AbstractName's with the same underlying 'A.QName'
--   that were brought into scope by different 'open' statements.
data Imported a = Imported
  { iWhere :: Int -- Position of 'Opened' extracted from the 'AbstractName'.
  , iThing :: a
  } deriving (Eq, Ord, Show)

instance Pretty a => Pretty (Imported a) where
  pretty (Imported i n) = pretty n <> " (at position " <> pretty i <> ")"

-- | Convert an 'AbstractName' or 'AbstractModule' to an 'Imported'
--   if it was brought into scope by an 'open' statement.
toImported :: Lineage a => a -> Maybe (Imported a)
toImported x = case lineage x of
  Opened m _ -> rangeToPosPos m <&> (`Imported` x)
  Applied{} -> Nothing
  Defined{} -> Nothing

-- Lenses for the components of the UnusedImportsState in the TCState.

stUnambiguousLookups :: Lens' TCState [AbstractName]
stUnambiguousLookups = stUnusedImportsState . lensUnambiguousLookups

stAmbiguousLookups :: Lens' TCState (IntMap (List2 AbstractName))
stAmbiguousLookups = stUnusedImportsState . lensAmbiguousLookups

stModuleLookups :: Lens' TCState [AbstractModule]
stModuleLookups = stUnusedImportsState . lensModuleLookups

stOpenedModules :: Lens' TCState (IntMap OpenedModule)
stOpenedModules = stUnusedImportsState . lensOpenedModules
