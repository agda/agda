{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs              #-}

{-| This module defines the notion of a scope and operations on scopes.
-}
module Agda.Syntax.Scope.Base where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ( (<>), null )
#else
import Prelude hiding ( null )
#endif

import Control.Arrow (first, second, (***))
import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Monad

import Data.Either (partitionEithers)
import Data.Function
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import qualified Data.Semigroup as Sgrp

import Data.Data (Data)

import Agda.Benchmarking

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Fixity as C

import Agda.Utils.AssocList (AssocList)
import qualified Agda.Utils.AssocList as AssocList
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.NonemptyList
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.Singleton
import qualified Agda.Utils.Map as Map

#include "undefined.h"
import Agda.Utils.Impossible

-- * Scope representation

-- | A scope is a named collection of names partitioned into public and private
--   names.
data Scope = Scope
      { scopeName           :: A.ModuleName
      , scopeParents        :: [A.ModuleName]
      , scopeNameSpaces     :: ScopeNameSpaces
      , scopeImports        :: Map C.QName A.ModuleName
      , scopeDatatypeModule :: Maybe DataOrRecord
      }
  deriving (Data, Eq, Show)

-- | See 'Agda.Syntax.Common.Access'.
data NameSpaceId
  = PrivateNS        -- ^ Things not exported by this module.
  | PublicNS         -- ^ Things defined and exported by this module.
  | ImportedNS       -- ^ Things from open public, exported by this module.
  | OnlyQualifiedNS  -- ^ Visible (as qualified) from outside,
                     --   but not exported when opening the module.
                     --   Used for qualified constructors.
  deriving (Data, Eq, Bounded, Enum, Show)

type ScopeNameSpaces = [(NameSpaceId, NameSpace)]

localNameSpace :: Access -> NameSpaceId
localNameSpace PublicAccess    = PublicNS
localNameSpace PrivateAccess{} = PrivateNS
localNameSpace OnlyQualified   = OnlyQualifiedNS

nameSpaceAccess :: NameSpaceId -> Access
nameSpaceAccess PrivateNS = PrivateAccess Inserted
nameSpaceAccess _         = PublicAccess

-- | Get a 'NameSpace' from 'Scope'.
scopeNameSpace :: NameSpaceId -> Scope -> NameSpace
scopeNameSpace ns = fromMaybe __IMPOSSIBLE__ . lookup ns . scopeNameSpaces

-- | A lens for 'scopeNameSpaces'
updateScopeNameSpaces :: (ScopeNameSpaces -> ScopeNameSpaces) -> Scope -> Scope
updateScopeNameSpaces f s = s { scopeNameSpaces = f (scopeNameSpaces s) }

-- | ``Monadic'' lens (Functor sufficient).
updateScopeNameSpacesM ::
  (Functor m) => (ScopeNameSpaces -> m ScopeNameSpaces) -> Scope -> m Scope
updateScopeNameSpacesM f s = for (f $ scopeNameSpaces s) $ \ x ->
  s { scopeNameSpaces = x }

-- | The complete information about the scope at a particular program point
--   includes the scope stack, the local variables, and the context precedence.
data ScopeInfo = ScopeInfo
      { scopeCurrent       :: A.ModuleName
      , scopeModules       :: Map A.ModuleName Scope
      , scopeVarsToBind    :: LocalVars
      , scopeLocals        :: LocalVars
      , scopePrecedence    :: PrecedenceStack
      , scopeInverseName   :: NameMap
      , scopeInverseModule :: ModuleMap
      , scopeInScope       :: InScopeSet
      , scopeFixities      :: C.Fixities    -- ^ Maps concrete names to fixities
      , scopePolarities    :: C.Polarities  -- ^ Maps concrete names to polarities
      }
  deriving (Data, Show)

type NameMap   = Map A.QName      (NonemptyList C.QName)
type ModuleMap = Map A.ModuleName [C.QName]
-- type ModuleMap = Map A.ModuleName (NonemptyList C.QName)

instance Eq ScopeInfo where
  ScopeInfo c1 m1 v1 l1 p1 _ _ _ _ _ == ScopeInfo c2 m2 v2 l2 p2 _ _ _ _ _ =
    c1 == c2 && m1 == m2 && v1 == v2 && l1 == l2 && p1 == p2

-- | Local variables.
type LocalVars = AssocList C.Name LocalVar

-- | For each bound variable, we want to know whether it was bound by a
--   λ, Π, module telescope, pattern, or @let@.
data Binder
  = LambdaBound  -- ^ @λ@ (currently also used for @Π@ and module parameters)
  | PatternBound -- ^ @f ... =@
  | LetBound     -- ^ @let ... in@
  deriving (Data, Show, Eq)

-- | A local variable can be shadowed by an import.
--   In case of reference to a shadowed variable, we want to report
--   a scope error.
data LocalVar = LocalVar
  { localVar        :: A.Name
    -- ^ Unique ID of local variable.
  , localBinder     :: Binder
    -- ^ Kind of binder used to introduce the variable (@λ@, @let@, ...).
  , localShadowedBy :: [AbstractName]
     -- ^ If this list is not empty, the local variable is
     --   shadowed by one or more imports.
  }
  deriving (Data, Show)

instance Eq LocalVar where
  (==) = (==) `on` localVar

instance Ord LocalVar where
  compare = compare `on` localVar

-- | We show shadowed variables as prefixed by a ".", as not in scope.
instance Pretty LocalVar where
  pretty (LocalVar x _ []) = pretty x
  pretty (LocalVar x _ xs) = "." <> pretty x

-- | Shadow a local name by a non-empty list of imports.
shadowLocal :: [AbstractName] -> LocalVar -> LocalVar
shadowLocal [] _ = __IMPOSSIBLE__
shadowLocal ys (LocalVar x b zs) = LocalVar x b (ys ++ zs)

-- | Treat patternBound variable as a module parameter
patternToModuleBound :: LocalVar -> LocalVar
patternToModuleBound x
 | localBinder x == PatternBound = x { localBinder = LambdaBound }
 | otherwise                     = x

-- | Project name of unshadowed local variable.
notShadowedLocal :: LocalVar -> Maybe A.Name
notShadowedLocal (LocalVar x _ []) = Just x
notShadowedLocal _ = Nothing

-- | Get all locals that are not shadowed __by imports__.
notShadowedLocals :: LocalVars -> AssocList C.Name A.Name
notShadowedLocals = mapMaybe $ \ (c,x) -> (c,) <$> notShadowedLocal x

-- | Lens for 'scopeVarsToBind'.
updateVarsToBind :: (LocalVars -> LocalVars) -> ScopeInfo -> ScopeInfo
updateVarsToBind f sc = sc { scopeVarsToBind = f (scopeVarsToBind sc) }

setVarsToBind :: LocalVars -> ScopeInfo -> ScopeInfo
setVarsToBind vars = updateVarsToBind (const vars)

-- | Lens for 'scopeLocals'.
updateScopeLocals :: (LocalVars -> LocalVars) -> ScopeInfo -> ScopeInfo
updateScopeLocals f sc = sc { scopeLocals = f (scopeLocals sc) }

setScopeLocals :: LocalVars -> ScopeInfo -> ScopeInfo
setScopeLocals vars = updateScopeLocals (const vars)

mapScopeInfo :: (Scope -> Scope) -> ScopeInfo -> ScopeInfo
mapScopeInfo f i = i{ scopeModules = f <$> scopeModules i }

------------------------------------------------------------------------
-- * Name spaces
--
-- Map concrete names to lists of abstract names.
------------------------------------------------------------------------

-- | A @NameSpace@ contains the mappings from concrete names that the user can
--   write to the abstract fully qualified names that the type checker wants to
--   read.
data NameSpace = NameSpace
      { nsNames   :: NamesInScope
        -- ^ Maps concrete names to a list of abstract names.
      , nsModules :: ModulesInScope
        -- ^ Maps concrete module names to a list of abstract module names.
      , nsInScope :: InScopeSet
      }
  deriving (Data, Eq, Show)

type ThingsInScope a = Map C.Name [a]
type NamesInScope    = ThingsInScope AbstractName
type ModulesInScope  = ThingsInScope AbstractModule
type InScopeSet      = Set A.QName

-- | Set of types consisting of exactly 'AbstractName' and 'AbstractModule'.
--
--   A GADT just for some dependent-types trickery.
data InScopeTag a where
  NameTag   :: InScopeTag AbstractName
  ModuleTag :: InScopeTag AbstractModule

-- | Type class for some dependent-types trickery.
class Eq a => InScope a where
  inScopeTag :: InScopeTag a

instance InScope AbstractName where
  inScopeTag = NameTag

instance InScope AbstractModule where
  inScopeTag = ModuleTag

-- | @inNameSpace@ selects either the name map or the module name map from
--   a 'NameSpace'.  What is selected is determined by result type
--   (using the dependent-type trickery).
inNameSpace :: forall a. InScope a => NameSpace -> ThingsInScope a
inNameSpace = case inScopeTag :: InScopeTag a of
  NameTag   -> nsNames
  ModuleTag -> nsModules

------------------------------------------------------------------------
-- * Decorated names
--
-- - What kind of name? (defined, constructor...)
-- - Where does the name come from? (to explain to user)
------------------------------------------------------------------------

-- | For the sake of parsing left-hand sides, we distinguish
--   constructor and record field names from defined names.
data KindOfName
  = ConName        -- ^ Constructor name.
  | FldName        -- ^ Record field name.
  | DefName        -- ^ Ordinary defined name.
  | PatternSynName -- ^ Name of a pattern synonym.
  | GeneralizeName -- ^ Name to be generalized
  | DisallowedGeneralizeName -- ^ Generalizable variable from a let open
  | MacroName      -- ^ Name of a macro
  | QuotableName   -- ^ A name that can only be quoted.
  deriving (Eq, Show, Data, Enum, Bounded)

-- | A list containing all name kinds.
allKindsOfNames :: [KindOfName]
allKindsOfNames = [minBound..maxBound]

-- | Where does a name come from?
--
--   This information is solely for reporting to the user,
--   see 'Agda.Interaction.InteractionTop.whyInScope'.
data WhyInScope
  = Defined
    -- ^ Defined in this module.
  | Opened C.QName WhyInScope
    -- ^ Imported from another module.
  | Applied C.QName WhyInScope
    -- ^ Imported by a module application.
  deriving (Data, Show)

-- | A decoration of 'Agda.Syntax.Abstract.Name.QName'.
data AbstractName = AbsName
  { anameName    :: A.QName
    -- ^ The resolved qualified name.
  , anameKind    :: KindOfName
    -- ^ The kind (definition, constructor, record field etc.).
  , anameLineage :: WhyInScope
    -- ^ Explanation where this name came from.
  , anameMetadata :: NameMetadata
    -- ^ Additional information needed during scope checking. Currently used
    --   for generalized data/record params.
  }
  deriving (Data, Show)

data NameMetadata = NoMetadata
                  | GeneralizedVarsMetadata (Map A.QName A.Name)
  deriving (Data, Show)

-- | A decoration of abstract syntax module names.
data AbstractModule = AbsModule
  { amodName    :: A.ModuleName
    -- ^ The resolved module name.
  , amodLineage :: WhyInScope
    -- ^ Explanation where this name came from.
  }
  deriving (Data, Show)

instance Eq AbstractName where
  (==) = (==) `on` anameName

instance Ord AbstractName where
  compare = compare `on` anameName

-- | Van Laarhoven lens on 'anameName'.
lensAnameName :: Functor m => (A.QName -> m A.QName) -> AbstractName -> m AbstractName
lensAnameName f am = f (anameName am) <&> \ m -> am { anameName = m }

instance Eq AbstractModule where
  (==) = (==) `on` amodName

instance Ord AbstractModule where
  compare = compare `on` amodName

-- | Van Laarhoven lens on 'amodName'.
lensAmodName :: Functor m => (A.ModuleName -> m A.ModuleName) -> AbstractModule -> m AbstractModule
lensAmodName f am = f (amodName am) <&> \ m -> am { amodName = m }


data ResolvedName
  = -- | Local variable bound by λ, Π, module telescope, pattern, @let@.
    VarName
    { resolvedVar      :: A.Name
    , resolvedBinder   :: Binder    -- ^ What kind of binder?
    }

  | -- | Function, data/record type, postulate.
    DefinedName Access AbstractName -- ^ 'anameKind' can be 'DefName', 'MacroName', 'QuotableName'.

  | -- | Record field name.  Needs to be distinguished to parse copatterns.
    FieldName (NonemptyList AbstractName)       -- ^ @('FldName' ==) . 'anameKind'@ for all names.

  | -- | Data or record constructor name.
    ConstructorName (NonemptyList AbstractName) -- ^ @('ConName' ==) . 'anameKind'@ for all names.

  | -- | Name of pattern synonym.
    PatternSynResName (NonemptyList AbstractName) -- ^ @('PatternSynName' ==) . 'anameKind'@ for all names.

  | -- | Unbound name.
    UnknownName
  deriving (Data, Show, Eq)

instance Pretty ResolvedName where
  pretty = \case
    VarName x _         -> "variable"    <+> pretty x
    DefinedName a x     -> pretty a           <+> pretty x
    FieldName xs        -> "field"       <+> pretty xs
    ConstructorName xs  -> "constructor" <+> pretty xs
    PatternSynResName x -> "pattern"     <+> pretty x
    UnknownName         -> "<unknown name>"

-- * Operations on name and module maps.

mergeNames :: Eq a => ThingsInScope a -> ThingsInScope a -> ThingsInScope a
mergeNames = Map.unionWith List.union

------------------------------------------------------------------------
-- * Operations on name spaces
------------------------------------------------------------------------

-- | The empty name space.
emptyNameSpace :: NameSpace
emptyNameSpace = NameSpace Map.empty Map.empty Set.empty


-- | Map functions over the names and modules in a name space.
mapNameSpace :: (NamesInScope   -> NamesInScope  ) ->
                (ModulesInScope -> ModulesInScope) ->
                (InScopeSet     -> InScopeSet    ) ->
                NameSpace -> NameSpace
mapNameSpace fd fm fs ns =
  ns { nsNames   = fd $ nsNames   ns
     , nsModules = fm $ nsModules ns
     , nsInScope = fs $ nsInScope ns
     }

-- | Zip together two name spaces.
zipNameSpace :: (NamesInScope   -> NamesInScope   -> NamesInScope  ) ->
                (ModulesInScope -> ModulesInScope -> ModulesInScope) ->
                (InScopeSet     -> InScopeSet     -> InScopeSet    ) ->
                NameSpace -> NameSpace -> NameSpace
zipNameSpace fd fm fs ns1 ns2 =
  ns1 { nsNames   = nsNames   ns1 `fd` nsNames   ns2
      , nsModules = nsModules ns1 `fm` nsModules ns2
      , nsInScope = nsInScope ns1 `fs` nsInScope ns2
      }

-- | Map monadic function over a namespace.
mapNameSpaceM :: Applicative m =>
  (NamesInScope   -> m NamesInScope  ) ->
  (ModulesInScope -> m ModulesInScope) ->
  (InScopeSet     -> m InScopeSet    ) ->
  NameSpace -> m NameSpace
mapNameSpaceM fd fm fs ns = update ns <$> fd (nsNames ns) <*> fm (nsModules ns) <*> fs (nsInScope ns)
  where
    update ns ds ms is = ns { nsNames = ds, nsModules = ms, nsInScope = is }

------------------------------------------------------------------------
-- * General operations on scopes
------------------------------------------------------------------------

-- | The empty scope.
emptyScope :: Scope
emptyScope = Scope
  { scopeName           = noModuleName
  , scopeParents        = []
  , scopeNameSpaces     = [ (nsid, emptyNameSpace) | nsid <- [minBound..maxBound] ]
  , scopeImports        = Map.empty
  , scopeDatatypeModule = Nothing
  }

-- | The empty scope info.
emptyScopeInfo :: ScopeInfo
emptyScopeInfo = ScopeInfo
  { scopeCurrent       = noModuleName
  , scopeModules       = Map.singleton noModuleName emptyScope
  , scopeVarsToBind    = []
  , scopeLocals        = []
  , scopePrecedence    = []
  , scopeInverseName   = Map.empty
  , scopeInverseModule = Map.empty
  , scopeInScope       = Set.empty
  , scopeFixities      = Map.empty
  , scopePolarities    = Map.empty
  }

-- | Map functions over the names and modules in a scope.
mapScope :: (NameSpaceId -> NamesInScope   -> NamesInScope  ) ->
            (NameSpaceId -> ModulesInScope -> ModulesInScope) ->
            (NameSpaceId -> InScopeSet    -> InScopeSet     ) ->
            Scope -> Scope
mapScope fd fm fs = updateScopeNameSpaces $ AssocList.mapWithKey mapNS
  where
    mapNS acc = mapNameSpace (fd acc) (fm acc) (fs acc)

-- | Same as 'mapScope' but applies the same function to all name spaces.
mapScope_ :: (NamesInScope   -> NamesInScope  ) ->
             (ModulesInScope -> ModulesInScope) ->
             (InScopeSet     -> InScopeSet    ) ->
             Scope -> Scope
mapScope_ fd fm fs = mapScope (const fd) (const fm) (const fs)

-- | Same as 'mapScope' but applies the function only on the given name space.
mapScope' :: NameSpaceId -> (NamesInScope   -> NamesInScope  ) ->
                            (ModulesInScope -> ModulesInScope) ->
                            (InScopeSet    -> InScopeSet     ) ->
                            Scope -> Scope
mapScope' i fd fm fs = mapScope (\ j -> if i == j then fd else id)
                                (\ j -> if i == j then fm else id)
                                (\ j -> if i == j then fs else id)

-- | Map monadic functions over the names and modules in a scope.
mapScopeM :: Applicative m =>
  (NameSpaceId -> NamesInScope   -> m NamesInScope  ) ->
  (NameSpaceId -> ModulesInScope -> m ModulesInScope) ->
  (NameSpaceId -> InScopeSet     -> m InScopeSet    ) ->
  Scope -> m Scope
mapScopeM fd fm fs = updateScopeNameSpacesM $ AssocList.mapWithKeyM mapNS
  where
    mapNS acc = mapNameSpaceM (fd acc) (fm acc) (fs acc)

-- | Same as 'mapScopeM' but applies the same function to both the public and
--   private name spaces.
mapScopeM_ :: Applicative m =>
  (NamesInScope   -> m NamesInScope  ) ->
  (ModulesInScope -> m ModulesInScope) ->
  (InScopeSet     -> m InScopeSet    ) ->
  Scope -> m Scope
mapScopeM_ fd fm fs = mapScopeM (const fd) (const fm) (const fs)

-- | Zip together two scopes. The resulting scope has the same name as the
--   first scope.
zipScope :: (NameSpaceId -> NamesInScope   -> NamesInScope   -> NamesInScope  ) ->
            (NameSpaceId -> ModulesInScope -> ModulesInScope -> ModulesInScope) ->
            (NameSpaceId -> InScopeSet     -> InScopeSet     -> InScopeSet    ) ->
            Scope -> Scope -> Scope
zipScope fd fm fs s1 s2 =
  s1 { scopeNameSpaces =
         [ (nsid, zipNS nsid ns1 ns2)
         | ((nsid, ns1), (nsid', ns2)) <-
             fromMaybe __IMPOSSIBLE__ $
               zipWith' (,) (scopeNameSpaces s1) (scopeNameSpaces s2)
         , assert (nsid == nsid')
         ]
     , scopeImports  = (Map.union `on` scopeImports)  s1 s2
     }
  where
    assert True  = True
    assert False = __IMPOSSIBLE__
    zipNS acc = zipNameSpace (fd acc) (fm acc) (fs acc)

-- | Same as 'zipScope' but applies the same function to both the public and
--   private name spaces.
zipScope_ :: (NamesInScope   -> NamesInScope   -> NamesInScope  ) ->
             (ModulesInScope -> ModulesInScope -> ModulesInScope) ->
             (InScopeSet     -> InScopeSet     -> InScopeSet    ) ->
             Scope -> Scope -> Scope
zipScope_ fd fm fs = zipScope (const fd) (const fm) (const fs)

-- | Recompute the inScope sets of a scope.
recomputeInScopeSets :: Scope -> Scope
recomputeInScopeSets = updateScopeNameSpaces (map $ second recomputeInScope)
  where
    recomputeInScope ns = ns { nsInScope = Set.unions $ map (Set.fromList . map anameName)
                                         $ Map.elems $ nsNames ns }

-- | Filter a scope keeping only concrete names matching the predicates.
--   The first predicate is applied to the names and the second to the modules.
filterScope :: (C.Name -> Bool) -> (C.Name -> Bool) -> Scope -> Scope
filterScope pd pm = recomputeInScopeSets .  mapScope_ (Map.filterKeys pd) (Map.filterKeys pm) id
  -- We don't have enough information in the in scope set to do an
  -- incremental update here, so just recompute it from the name map.

-- | Return all names in a scope.
allNamesInScope :: InScope a => Scope -> ThingsInScope a
allNamesInScope = namesInScope [minBound..maxBound]

allNamesInScope' :: InScope a => Scope -> ThingsInScope (a, Access)
allNamesInScope' s =
  foldr1 mergeNames [ map (, nameSpaceAccess ns) <$> namesInScope [ns] s
                    | ns <- [minBound..maxBound] ]

-- | Returns the scope's non-private names.
exportedNamesInScope :: InScope a => Scope -> ThingsInScope a
exportedNamesInScope = namesInScope [PublicNS, ImportedNS, OnlyQualifiedNS]

namesInScope :: InScope a => [NameSpaceId] -> Scope -> ThingsInScope a
namesInScope ids s =
  foldr1 mergeNames [ inNameSpace (scopeNameSpace nsid s) | nsid <- ids ]

allThingsInScope :: Scope -> NameSpace
allThingsInScope = thingsInScope [minBound..maxBound]

thingsInScope :: [NameSpaceId] -> Scope -> NameSpace
thingsInScope fs s =
  NameSpace { nsNames   = namesInScope fs s
            , nsModules = namesInScope fs s
            , nsInScope = Set.unions [ nsInScope $ scopeNameSpace nsid s | nsid <- fs ]
            }

-- | Merge two scopes. The result has the name of the first scope.
mergeScope :: Scope -> Scope -> Scope
mergeScope = zipScope_ mergeNames mergeNames Set.union

-- | Merge a non-empty list of scopes. The result has the name of the first
--   scope in the list.
mergeScopes :: [Scope] -> Scope
mergeScopes [] = __IMPOSSIBLE__
mergeScopes ss = foldr1 mergeScope ss

-- * Specific operations on scopes

-- | Move all names in a scope to the given name space (except never move from
--   Imported to Public).
setScopeAccess :: NameSpaceId -> Scope -> Scope
setScopeAccess a s = (`updateScopeNameSpaces` s) $ AssocList.mapWithKey $ const . ns
  where
    zero  = emptyNameSpace
    one   = allThingsInScope s
    imp   = thingsInScope [ImportedNS] s
    noimp = thingsInScope [PublicNS, PrivateNS, OnlyQualifiedNS] s

    ns b = case (a, b) of
      (PublicNS, PublicNS)   -> noimp
      (PublicNS, ImportedNS) -> imp
      _ | a == b             -> one
        | otherwise          -> zero

-- | Update a particular name space.
setNameSpace :: NameSpaceId -> NameSpace -> Scope -> Scope
setNameSpace nsid ns = modifyNameSpace nsid $ const ns

-- | Modify a particular name space.
modifyNameSpace :: NameSpaceId -> (NameSpace -> NameSpace) -> Scope -> Scope
modifyNameSpace nsid f = updateScopeNameSpaces $ AssocList.updateAt nsid f

-- | Add names to a scope.
addNamesToScope :: NameSpaceId -> C.Name -> [AbstractName] -> Scope -> Scope
addNamesToScope acc x ys s = mergeScope s s1
  where
    s1 = setScopeAccess acc $ setNameSpace PublicNS ns emptyScope
    ns = emptyNameSpace { nsNames   = Map.singleton x ys
                        , nsInScope = Set.fromList (map anameName ys) }

-- | Add a name to a scope.
addNameToScope :: NameSpaceId -> C.Name -> AbstractName -> Scope -> Scope
addNameToScope acc x y s = addNamesToScope acc x [y] s

-- | Remove a name from a scope. Caution: does not update the nsInScope set.
--   This is only used by rebindName and in that case we add the name right
--   back (but with a different kind).
removeNameFromScope :: NameSpaceId -> C.Name -> Scope -> Scope
removeNameFromScope ns x s = mapScope remove (const id) (const id) s
  where
    remove ns' | ns' /= ns = id
               | otherwise = Map.delete x

-- | Add a module to a scope.
addModuleToScope :: NameSpaceId -> C.Name -> AbstractModule -> Scope -> Scope
addModuleToScope acc x m s = mergeScope s s1
  where
    s1 = setScopeAccess acc $ setNameSpace PublicNS ns emptyScope
    ns = emptyNameSpace { nsModules = Map.singleton x [m] }

-- When we get here we cannot have both using and hiding
type UsingOrHiding = Either C.Using [C.ImportedName]

usingOrHiding :: C.ImportDirective -> UsingOrHiding
usingOrHiding i =
  case (using i, hiding i) of
    (UseEverything, xs) -> Right xs
    (u, [])             -> Left u
    _                   -> __IMPOSSIBLE__

-- | Apply an 'ImportDirective' to a scope.
applyImportDirective :: C.ImportDirective -> Scope -> Scope
applyImportDirective dir s = mergeScope usedOrHidden renamed
  where
    usedOrHidden = useOrHide (hideLHS (impRenaming dir) $ usingOrHiding dir) s
    renamed      = rename (impRenaming dir) $ useOrHide useRenamedThings s

    useRenamedThings = Left $ Using $ map renFrom $ impRenaming dir

    hideLHS :: [C.Renaming] -> UsingOrHiding -> UsingOrHiding
    hideLHS _   i@(Left _) = i
    hideLHS ren (Right xs) = Right $ xs ++ map renFrom ren

    useOrHide :: UsingOrHiding -> Scope -> Scope
    useOrHide (Right xs)        s = filterNames notElem notElem xs s
    useOrHide (Left (Using xs)) s = filterNames elem    elem    xs s
    useOrHide _                 _ = __IMPOSSIBLE__

    filterNames :: (C.Name -> [C.Name] -> Bool) ->
                   (C.Name -> [C.Name] -> Bool) ->
                   [C.ImportedName] -> Scope -> Scope
    filterNames pd pm xs = filterScope (`pd` ds) (`pm` ms)
      where
        ds = [ x | ImportedName   x <- xs ]
        ms = [ m | ImportedModule m <- xs ]

    -- Renaming
    rename :: [C.Renaming] -> Scope -> Scope
    rename rho = mapScope_ (Map.mapKeys $ ren drho)
                           (Map.mapKeys $ ren mrho)
                           id
      where
        (drho, mrho) = partitionEithers $ for rho $ \case
          Renaming (ImportedName   x) (ImportedName   y) _ -> Left  (x,y)
          Renaming (ImportedModule x) (ImportedModule y) _ -> Right (x,y)
          _ -> __IMPOSSIBLE__

        ren r x = fromMaybe x $ lookup x r

-- | Rename the abstract names in a scope.
renameCanonicalNames :: Map A.QName A.QName -> Map A.ModuleName A.ModuleName ->
                        Scope -> Scope
renameCanonicalNames renD renM = mapScope_ renameD renameM (Set.map newName)
  where
    newName x = Map.findWithDefault x x renD
    newMod  x = Map.findWithDefault x x renM

    renameD = Map.map $ map $ over lensAnameName newName
    renameM = Map.map $ map $ over lensAmodName  newMod

-- | Remove private name space of a scope.
--
--   Should be a right identity for 'exportedNamesInScope'.
--   @exportedNamesInScope . restrictPrivate == exportedNamesInScope@.
restrictPrivate :: Scope -> Scope
restrictPrivate s = setNameSpace PrivateNS emptyNameSpace
                  $ s { scopeImports = Map.empty }

-- | Remove private things from the given module from a scope.
restrictLocalPrivate :: ModuleName -> Scope -> Scope
restrictLocalPrivate m = mapScope' PrivateNS (Map.mapMaybe rName) (Map.mapMaybe rMod)
                                             (Set.filter (not . (`isInModule` m)))
  where
    check p x = x <$ guard (p x)
    rName as = check (not . null) $ filter (not . (`isInModule`    m) . anameName) as
    rMod  as = check (not . null) $ filter (not . (`isSubModuleOf` m) . amodName)  as

-- | Remove names that can only be used qualified (when opening a scope)
removeOnlyQualified :: Scope -> Scope
removeOnlyQualified s = setNameSpace OnlyQualifiedNS emptyNameSpace s

-- | Disallow using generalized variables from the scope
disallowGeneralizedVars :: Scope -> Scope
disallowGeneralizedVars = mapScope_ ((fmap . map) disallow) id id
  where
    disallow a = a { anameKind = disallowGen (anameKind a) }
    disallowGen GeneralizeName = DisallowedGeneralizeName
    disallowGen k              = k

-- | Add an explanation to why things are in scope.
inScopeBecause :: (WhyInScope -> WhyInScope) -> Scope -> Scope
inScopeBecause f = mapScope_ mapName mapMod id
  where
    mapName = fmap . map $ \a -> a { anameLineage = f $ anameLineage a }
    mapMod  = fmap . map $ \a -> a { amodLineage  = f $ amodLineage a  }

-- | Get the public parts of the public modules of a scope
publicModules :: ScopeInfo -> Map A.ModuleName Scope
publicModules scope = Map.filterWithKey (\ m _ -> reachable m) allMods
  where
    -- Get all modules in the ScopeInfo.
    allMods   = Map.map restrictPrivate $ scopeModules scope
    root      = scopeCurrent scope

    modules s = map amodName $ concat $ Map.elems $ allNamesInScope s

    chase m = m : concatMap chase ms
      where ms = maybe __IMPOSSIBLE__ modules $ Map.lookup m allMods

    reachable = (`elem` chase root)

publicNames :: ScopeInfo -> Set AbstractName
publicNames scope =
  Set.fromList $ concat $ Map.elems $
  exportedNamesInScope $ mergeScopes $ Map.elems $ publicModules scope

everythingInScope :: ScopeInfo -> NameSpace
everythingInScope scope = allThingsInScope $ mergeScopes $
    (s0 :) $ map look $ scopeParents s0
  where
    look m = fromMaybe __IMPOSSIBLE__ $ Map.lookup m $ scopeModules scope
    s0     = look $ scopeCurrent scope

everythingInScopeQualified :: ScopeInfo -> NameSpace
everythingInScopeQualified scope =
  allThingsInScope $ mergeScopes $
    chase Set.empty scopes
  where
    s0      = look $ scopeCurrent scope
    scopes  = s0 : map look (scopeParents s0)
    look m  = fromMaybe __IMPOSSIBLE__ $ Map.lookup m $ scopeModules scope
    lookP   = restrictPrivate . look

    -- We start with the current module and all its parents and look through
    -- all their imports and submodules.
    chase seen [] = []
    chase seen (s : ss)
      | Set.member name seen = chase seen ss
      | otherwise = s : chase (Set.insert name seen) (imports ++ submods ++ ss)
      where
        name    = scopeName s
        imports = map lookP $ Map.elems $ scopeImports s
        submods = map (lookP . amodName) $ concat $ Map.elems $ allNamesInScope s

-- | Compute a flattened scope. Only include unqualified names or names
-- qualified by modules in the first argument.
flattenScope :: [[C.Name]] -> ScopeInfo -> Map C.QName [AbstractName]
flattenScope ms scope =
  Map.unionWith (++)
    (build ms allNamesInScope root)
    imported
  where
    current = moduleScope $ scopeCurrent scope
    root    = mergeScopes $ current : map moduleScope (scopeParents current)

    imported = Map.unionsWith (++)
               [ qual c (build ms' exportedNamesInScope $ moduleScope a)
               | (c, a) <- Map.toList $ scopeImports root
               , let -- get the suffixes of c in ms
                     ms' = mapMaybe (List.stripPrefix $ C.qnameParts c) ms
               , not $ null ms' ]
    qual c = Map.mapKeys (q c)
      where
        q (C.QName x)  = C.Qual x
        q (C.Qual m x) = C.Qual m . q x

    build :: [[C.Name]] -> (forall a. InScope a => Scope -> ThingsInScope a) -> Scope -> Map C.QName [AbstractName]
    build ms getNames s = Map.unionsWith (++) $
        (Map.mapKeysMonotonic C.QName $ getNames s) :
          [ Map.mapKeysMonotonic (\ y -> C.Qual x y) $
              build ms' exportedNamesInScope $ moduleScope m
          | (x, mods) <- Map.toList (getNames s)
          , let ms' = [ tl | hd:tl <- ms, hd == x ]
          , not $ null ms'
          , AbsModule m _ <- mods ]

    moduleScope :: A.ModuleName -> Scope
    moduleScope m = fromMaybe __IMPOSSIBLE__ $ Map.lookup m $ scopeModules scope

-- | Get all concrete names in scope. Includes bound variables.
concreteNamesInScope :: ScopeInfo -> Set C.QName
concreteNamesInScope scope =
  Set.unions [ build allNamesInScope root, imported, locals ]
  where
    current = moduleScope $ scopeCurrent scope
    root    = mergeScopes $ current : map moduleScope (scopeParents current)

    locals  = Set.fromList [ C.QName x | (x, _) <- scopeLocals scope ]

    imported = Set.unions
               [ qual c (build exportedNamesInScope $ moduleScope a)
               | (c, a) <- Map.toList $ scopeImports root ]
    qual c = Set.map (q c)
      where
        q (C.QName x)  = C.Qual x
        q (C.Qual m x) = C.Qual m . q x

    build :: (forall a. InScope a => Scope -> ThingsInScope a) -> Scope -> Set C.QName
    build getNames s = Set.unions $
        (Set.fromList $ map C.QName $ Map.keys (getNames s :: ThingsInScope AbstractName)) :
          [ Set.mapMonotonic (\ y -> C.Qual x y) $
              build exportedNamesInScope $ moduleScope m
          | (x, mods) <- Map.toList (getNames s)
          , prettyShow x /= "_"
          , AbsModule m _ <- mods ]

    moduleScope :: A.ModuleName -> Scope
    moduleScope m = fromMaybe __IMPOSSIBLE__ $ Map.lookup m $ scopeModules scope

-- | Look up a name in the scope
scopeLookup :: InScope a => C.QName -> ScopeInfo -> [a]
scopeLookup q scope = map fst $ scopeLookup' q scope

scopeLookup' :: forall a. InScope a => C.QName -> ScopeInfo -> [(a, Access)]
scopeLookup' q scope =
  List.nubBy ((==) `on` fst) $
    findName q root ++ maybeToList topImports ++ imports
  where

    -- 1. Finding a name in the current scope and its parents.

    moduleScope :: A.ModuleName -> Scope
    moduleScope m = fromMaybe __IMPOSSIBLE__ $ Map.lookup m $ scopeModules scope

    current :: Scope
    current = moduleScope $ scopeCurrent scope

    root    :: Scope
    root    = mergeScopes $ current : map moduleScope (scopeParents current)

    -- | Find a concrete, possibly qualified name in scope @s@.
    findName :: forall a. InScope a => C.QName -> Scope -> [(a, Access)]
    findName q0 s = case q0 of
      C.QName x  -> lookupName x s
      C.Qual x q -> do
        let -- | Get the modules named @x@ in scope @s@.
            mods :: [A.ModuleName]
            mods = amodName . fst <$> lookupName x s
            -- | Get the definitions named @x@ in scope @s@ and interpret them as modules.
            -- Andreas, 2013-05-01: Issue 836 debates this feature:
            -- Qualified constructors are qualified by their datatype rather than a module
            defs :: [A.ModuleName]
            defs = mnameFromList . qnameToList . anameName . fst <$> lookupName x s
        -- Andreas, 2013-05-01:  Issue 836 complains about the feature
        -- that constructors can also be qualified by their datatype
        -- and projections by their record type.  This feature is off
        -- if we just consider the modules:
        m <- mods
        -- The feature is on if we consider also the data and record types:
        -- trace ("mods ++ defs = " ++ show (mods ++ defs)) $ do
        -- m <- nub $ mods ++ defs -- record types will appear both as a mod and a def
        -- Get the scope of module m, if any, and remove its private definitions.
        let ss  = Map.lookup m $ scopeModules scope
            ss' = restrictPrivate <$> ss
        -- trace ("ss  = " ++ show ss ) $ do
        -- trace ("ss' = " ++ show ss') $ do
        s' <- maybeToList ss'
        findName q s'
      where
        lookupName :: forall a. InScope a => C.Name -> Scope -> [(a, Access)]
        lookupName x s = fromMaybe [] $ Map.lookup x $ allNamesInScope' s

    -- 2. Finding a name in the top imports.

    topImports :: Maybe (a, Access)
    topImports = case (inScopeTag :: InScopeTag a) of
      NameTag   -> Nothing
      ModuleTag -> first (`AbsModule` Defined) <$> imported q

    imported :: C.QName -> Maybe (A.ModuleName, Access)
    imported q = fmap (,PublicAccess) $ Map.lookup q $ scopeImports root

    -- 3. Finding a name in the imports belonging to an initial part of the qualifier.

    imports :: [(a, Access)]
    imports = do
      (m, x) <- splitName q
      m <- maybeToList $ fst <$> imported m
      findName x $ restrictPrivate $ moduleScope m

    -- return all possible splittings, e.g.
    -- splitName X.Y.Z = [(X, Y.Z), (X.Y, Z)]
    splitName :: C.QName -> [(C.QName, C.QName)]
    splitName (C.QName x)  = []
    splitName (C.Qual x q) =
      (C.QName x, q) : [ (C.Qual x m, r) | (m, r) <- splitName q ]


-- * Inverse look-up

data AllowAmbiguousNames
  = AmbiguousAnything
      -- ^ Used for instance arguments to check whether a name is in scope,
      --   but we do not care whether is is ambiguous
  | AmbiguousConProjs
      -- ^ Ambiguous constructors, projections, or pattern synonyms.
  | AmbiguousNothing
  deriving (Eq)

isNameInScope :: A.QName -> ScopeInfo -> Bool
isNameInScope q scope =
  billToPure [ Scoping, InverseScopeLookup ] $
  Set.member q (scopeInScope scope)

-- | Find the concrete names that map (uniquely) to a given abstract name.
--   Sort by length, shortest first.

inverseScopeLookup :: Either A.ModuleName A.QName -> ScopeInfo -> [C.QName]
inverseScopeLookup = inverseScopeLookup' AmbiguousConProjs

inverseScopeLookup' :: AllowAmbiguousNames -> Either A.ModuleName A.QName -> ScopeInfo -> [C.QName]
inverseScopeLookup' amb name scope = billToPure [ Scoping , InverseScopeLookup ] $
  case name of
    Left  m -> best $ filter unambiguousModule $ findModule m
    Right q -> best $ filter unambiguousName   $ findName q
  where
    findName   x = maybe [] toList $ Map.lookup x (scopeInverseName scope)
    findModule x = fromMaybe []    $ Map.lookup x (scopeInverseModule scope)

    len :: C.QName -> Int
    len (C.QName _)  = 1
    len (C.Qual _ x) = 1 + len x

    best :: [C.QName] -> [C.QName]
    best = List.sortBy (compare `on` len)

    unique :: forall a . [a] -> Bool
    unique []      = __IMPOSSIBLE__
    unique [_]     = True
    unique (_:_:_) = False

    unambiguousModule q = amb == AmbiguousAnything || unique (scopeLookup q scope :: [AbstractModule])
    unambiguousName   q = amb == AmbiguousAnything
        || unique xs
        || amb == AmbiguousConProjs
           && or [ all ((kind ==) . anameKind) xs | kind <- [ConName, FldName, PatternSynName] ]
      where xs = scopeLookup q scope

recomputeInverseScopeMaps :: ScopeInfo -> ScopeInfo
recomputeInverseScopeMaps scope = billToPure [ Scoping , InverseScopeLookup ] $
  scope { scopeInverseName   = nameMap
        , scopeInverseModule = Map.fromList [ (x, findModule x) | x <- Map.keys moduleMap ++ Map.keys importMap ]
        , scopeInScope       = nsInScope $ everythingInScopeQualified scope
        }
  where
    this = scopeCurrent scope
    current = this : scopeParents (moduleScope this)
    scopes  = [ (m, restrict m s) | (m, s) <- Map.toList (scopeModules scope) ]

    moduleScope :: A.ModuleName -> Scope
    moduleScope m = fromMaybe __IMPOSSIBLE__ $ Map.lookup m $ scopeModules scope

    restrict m s | m `elem` current = s
                 | otherwise = restrictPrivate s

    internalName :: C.QName -> Bool
    internalName C.QName{} = False
    internalName (C.Qual m n) = intern m || internalName n
      where
      -- Recognize fresh names created Parser.y
      intern (C.Name _ _ [ C.Id ('.' : '#' : _) ]) = True
      intern _ = False

    findName :: Ord a => Map a [(A.ModuleName, C.Name)] -> a -> [C.QName]
    findName table q = do
      (m, x) <- fromMaybe [] $ Map.lookup q table
      if m `elem` current
        then return (C.QName x)
        else do
          y <- findModule m
          let z = C.qualify y x
          guard $ not $ internalName z
          return z

    findModule :: A.ModuleName -> [C.QName]
    findModule q = findName moduleMap q ++
                   fromMaybe [] (Map.lookup q importMap)

    importMap = Map.fromListWith (++) $ do
      (m, s) <- scopes
      (x, y) <- Map.toList $ scopeImports s
      return (y, singleton x)

    moduleMap = Map.fromListWith (++) $ do
      (m, s)  <- scopes
      (x, ms) <- Map.toList (allNamesInScope s)
      q       <- amodName <$> ms
      return (q, singleton (m, x))

    nameMap :: NameMap
    nameMap = Map.fromListWith (Sgrp.<>) $ do
      (m, s)  <- scopes
      (x, ms) <- Map.toList (allNamesInScope s)
      q       <- anameName <$> ms
      if elem m current
        then return (q, singleton (C.QName x))
        else do
          y <- findModule m
          let z = C.qualify y x
          guard $ not $ internalName z
          return (q, singleton z)

-- | Find the concrete names that map (uniquely) to a given abstract qualified name.
--   Sort by length, shortest first.
inverseScopeLookupName :: A.QName -> ScopeInfo -> [C.QName]
inverseScopeLookupName x = inverseScopeLookup (Right x)

inverseScopeLookupName' :: AllowAmbiguousNames -> A.QName -> ScopeInfo -> [C.QName]
inverseScopeLookupName' ambCon x = inverseScopeLookup' ambCon (Right x)

-- | Find the concrete names that map (uniquely) to a given abstract module name.
--   Sort by length, shortest first.
inverseScopeLookupModule :: A.ModuleName -> ScopeInfo -> [C.QName]
inverseScopeLookupModule x = inverseScopeLookup (Left x)

------------------------------------------------------------------------
-- * (Debug) printing
------------------------------------------------------------------------

instance Pretty AbstractName where
  pretty = pretty . anameName

instance Pretty AbstractModule where
  pretty = pretty . amodName

instance Pretty NameSpaceId where
  pretty = text . \case
    PublicNS        -> "public"
    PrivateNS       -> "private"
    ImportedNS      -> "imported"
    OnlyQualifiedNS -> "only-qualified"

instance Pretty NameSpace where
  pretty = vcat . prettyNameSpace

prettyNameSpace :: NameSpace -> [Doc]
prettyNameSpace (NameSpace names mods _) =
    blockOfLines "names"   (map pr $ Map.toList names) ++
    blockOfLines "modules" (map pr $ Map.toList mods)
  where
    pr :: (Pretty a, Pretty b) => (a,b) -> Doc
    pr (x, y) = pretty x <+> "-->" <+> pretty y

instance Pretty Scope where
  pretty (scope@Scope{ scopeName = name, scopeParents = parents, scopeImports = imps }) =
    vcat $
      [ "scope" <+> pretty name ] ++ ind (
        concat [ blockOfLines (pretty nsid) $ prettyNameSpace $ scopeNameSpace nsid scope
               | nsid <- [minBound..maxBound] ]
      ++ blockOfLines "imports"
           (case Map.keys imps of [] -> []; ks -> [ prettyList ks ])
      )
    where ind = map $ nest 2

-- | Add first string only if list is non-empty.
blockOfLines :: Doc -> [Doc] -> [Doc]
blockOfLines _  [] = []
blockOfLines hd ss = hd : map (nest 2) ss

instance Pretty ScopeInfo where
  pretty (ScopeInfo this mods toBind locals ctx _ _ _ _ _) = vcat $
    [ "ScopeInfo"
    , "  current = " <> pretty this
    ] ++
    (if null toBind then [] else [ "  toBind  = " <> pretty locals ]) ++
    (if null locals then [] else [ "  locals  = " <> pretty locals ]) ++
    [ "  context = " <> pretty ctx
    , "  modules"
    ] ++
    map (nest 4) (List.filter (not . null) $ map pretty $ Map.elems mods)

------------------------------------------------------------------------
-- * Boring instances
------------------------------------------------------------------------

instance KillRange ScopeInfo where
  killRange m = m

instance HasRange AbstractName where
  getRange = getRange . anameName

instance SetRange AbstractName where
  setRange r x = x { anameName = setRange r $ anameName x }
