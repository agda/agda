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
import Agda.Syntax.Common ( IsInstanceDef(isInstanceDef), IsInstance )
import Agda.Syntax.Common.Pretty (prettyShow, Pretty (pretty))
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Position ( HasRange(getRange), SetRange(setRange), Range )
import Agda.Syntax.Position qualified as P
import Agda.Syntax.Scope.Base as A

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Trace (setCurrentRange)
import Agda.TypeChecking.Warnings (warning)

import Agda.Utils.Boolean ( (||) )
import Agda.Utils.Lens
import Agda.Utils.List (partitionMaybe)
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
    unamb = modifyTCLens stUnambiguousLookups . (:)
    amb = modifyTCLens stAmbiguousLookups . IntMap.insert i
    -- The range
    i = fromMaybe __IMPOSSIBLE__ $ rangeToPosPos x

rangeToPosPos :: HasRange a => a -> Maybe Int
rangeToPosPos = fmap (fromIntegral . P.posPos) . P.rStart' . getRange

-- | Call this when opening a module with all the names it brings into scope.
openedModule :: A.ModuleName -> C.QName -> Scope -> ScopeM ()
openedModule currentModule x (Scope m0 _parents ns imports _dataOrRec) = do
  -- @imports@ have been removed by 'restrictPrivate'.
  unless (null imports) __IMPOSSIBLE__

  -- When the UnusedImports warning is off, do not collect information about @open@.
  -- E.g. we do not want to see warnings for the automatically inserted
  -- @open import Agda.Primitive using (Set)@.
  doWarn :: Bool <- useTC $ stPragmaOptions . lensOptWarningMode . lensSingleWarning UnusedImports_
  reportSLn "warning.unusedImports" 20 $ unlines
    [ "openedModule: " <> prettyShow doWarn
    -- , "currentModule: " <> prettyShow curM
    ]
  when doWarn do
    let
      m = setRange (getRange x) m0
      broughtIntoScope :: NamesInScope -- [Map C.Name (List1 AbstractName)]
      broughtIntoScope = mergeNamesMany $ map (nsNames . snd) ns
      k = fromMaybe __IMPOSSIBLE__ $ rangeToPosPos x
    modifyTCLens stOpenedModules $ IntMap.insert k (m, currentModule, broughtIntoScope)

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

toImportedName :: AbstractName -> Maybe ImportedName
toImportedName x = case anameLineage x of
  Opened m _ -> rangeToPosPos m <&> (`ImportedName` x)
  Applied{} -> Nothing
  Defined{} -> Nothing

-- | Call this when a file has been checked.
warnUnusedImports :: TCM ()
warnUnusedImports = do
    st <- useTC stUnusedImportsState
    disambiguatedNames <- useTC stDisambiguatedNames
    -- If instances can be used qualified, they do not need to be imported,
    -- so we should warn about them.
    qualifiedInstances <- optQualifiedInstances <$> pragmaOptions

    reportSLn "warning.unusedImports" 60 $ "unambiguousLookups: " <> prettyShow (unambiguousLookups st)

    -- Disambiguate overloaded lookups.
    let
      helper =  \ (i :: Int) (ys :: List2 AbstractName) -> do
        case IntMap.lookup i disambiguatedNames of
          Just (DisambiguatedName _k x) -> (filter ((x ==) . anameName) (List2.toList ys) ++)
          Nothing -> (List2.toList ys ++) -- __IMPOSSIBLE__
      allLookups :: [AbstractName]
      allLookups = IntMap.foldrWithKey helper (unambiguousLookups st) (ambiguousLookups st)

    -- Compute unambiguous lookups by using name disambiguation info from type checker.
    let
      lookups :: [ImportedName]
      (unknowns, lookups) = partitionMaybe toImportedName allLookups
      lookupSet :: Set ImportedName
      lookupSet = Set.fromList lookups
      isLookedUp, isInst, isUsed  :: ImportedName -> Bool
      isLookedUp = (`Set.member` lookupSet)
      isInst = isJust . isInstanceDef
      isUsed = if qualifiedInstances then isLookedUp else isInst || isLookedUp

    reportSLn "warning.unusedImports" 60 $ "allLookups: " <> prettyShow allLookups
    reportSLn "warning.unusedImports" 60 $ "lookups: " <> prettyShow lookups
    reportSLn "warning.unusedImports" 60 $ "unknowns: " <> prettyShow unknowns
    -- unless (null unknowns) do
    --   reportSLn "warning.unusedImports" 60 $ "unknowns: " <> show unknowns
    --   __IMPOSSIBLE__

    forM_ (openedModules st) \ (m :: A.ModuleName, parent :: A.ModuleName, sc :: NamesInScope) -> do
      let
        f :: (C.Name, List1 AbstractName) -> Maybe (C.Name, List1 ImportedName)
        f = traverse $ traverse toImportedName
        -- f (x, ys) = (x ,) <$> traverse toImportedName ys
        imps :: [(C.Name, List1 ImportedName)]
        (other, imps) = partitionMaybe f $ Map.toList sc
        used, unused :: [(C.Name, List1 ImportedName)]
        imps' = map (\ (x, ys) -> (x, setRange (getRange x) <$> ys)) imps
        (used, unused) = partition (\ (x :: C.Name, ys :: List1 ImportedName) -> any isUsed ys) imps'
        warn = setCurrentRange m . withCurrentModule parent . warning . UnusedImports m

      reportSLn "warning.unusedImports" 60 $ "used: " <> prettyShow used
      reportSLn "warning.unusedImports" 60 $ "unused: " <> prettyShow unused
      unless (null other) do
        __IMPOSSIBLE_VERBOSE__ (show other)
      if null used then warn Nothing else
        List1.unlessNull (map snd unused) \ unused1 -> do
          warn $ Just $ fmap (iName . List1.head) unused1

stUnambiguousLookups :: Lens' TCState [AbstractName]
stUnambiguousLookups = stUnusedImportsState . lensUnambiguousLookups

stAmbiguousLookups :: Lens' TCState (IntMap (List2 AbstractName))
stAmbiguousLookups = stUnusedImportsState . lensAmbiguousLookups

stOpenedModules :: Lens' TCState (IntMap (A.ModuleName, A.ModuleName, NamesInScope))
stOpenedModules = stUnusedImportsState . lensOpenedModules
