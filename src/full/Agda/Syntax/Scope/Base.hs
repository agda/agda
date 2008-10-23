{-# LANGUAGE CPP, DeriveDataTypeable #-}

{-| This module defines the notion of a scope and operations on scopes.
-}
module Agda.Syntax.Scope.Base where

import Data.Generics (Typeable, Data)
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Function

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Concrete (ImportDirective(..), UsingOrHiding(..), ImportedName(..))
import qualified Agda.Utils.Map as Map
import Agda.Utils.Tuple

#include "../../undefined.h"
import Agda.Utils.Impossible

-- * Scope representation

-- | A scope is a named collection of names partitioned into public and private
--   names.
data Scope = Scope
      { scopeName    :: A.ModuleName
      , scopePrivate :: NameSpace
      , scopePublic  :: NameSpace
      }
  deriving (Typeable, Data)

-- | The scope at a particular point in the program is determined by the stack
--   of all enclosing scopes.
type ScopeStack = [Scope]

-- | The complete information about the scope at a particular program point
--   includes the scope stack, the local variables, and the context precedence.
data ScopeInfo = ScopeInfo
      { scopeStack	:: ScopeStack
      , scopeLocals	:: LocalVars
      , scopePrecedence :: Precedence
      }
  deriving (Typeable, Data)

-- | Local variables
type LocalVars = [(C.Name, A.Name)]

-- | A @NameSpace@ contains the mappings from concrete names that the user can
--   write to the abstract fully qualified names that the type checker wants to
--   read.
data NameSpace = NameSpace
      { nsNames	  :: NamesInScope
      , nsModules :: ModulesInScope
      }
  deriving (Typeable, Data)

type NamesInScope   = Map C.QName [AbstractName]
type ModulesInScope = Map C.QName [AbstractModule]

-- | We distinguish constructor names from other names.
data KindOfName = ConName | DefName
  deriving (Eq, Show, Typeable, Data)

-- | Apart from the name, we also record whether it's a constructor or not and
--   what the fixity is.
data AbstractName = AbsName
      { anameName   :: A.QName
      , anameKind   :: KindOfName
      }
  deriving (Typeable, Data)

-- | For modules we record the arity. I'm not sure that it's every used anywhere.
data AbstractModule = AbsModule
      { amodName    :: A.ModuleName
      }
  deriving (Typeable, Data)

instance Eq AbstractName where
  (==) = (==) `on` anameName

instance Ord AbstractName where
  compare = compare `on` anameName

instance Eq AbstractModule where
  (==) = (==) `on` amodName

instance Ord AbstractModule where
  compare = compare `on` amodName

instance Show ScopeInfo where
  show (ScopeInfo stack locals ctx) =
    unlines $
      [ "ScopeInfo" ] ++
      (if null locals then [] else [ "  locals  = " ++ show locals ]) ++
      [ "  context = " ++ show ctx
      , "  stack"
      ] ++ map ("    "++) (relines . map show $ stack)
    where
      relines = filter (not . null) . lines . unlines

blockOfLines :: String -> [String] -> [String]
blockOfLines _  [] = []
blockOfLines hd ss = hd : map ("  "++) ss

instance Show Scope where
  show (Scope { scopeName = name, scopePublic = pub, scopePrivate = pri }) =
    unlines $
      [ "scope " ++ show name ]
      ++ blockOfLines "public"  (lines $ show pub)
      ++ blockOfLines "private" (lines $ show pri)

instance Show NameSpace where
  show (NameSpace names mods) =
    unlines $
      blockOfLines "names"   (map pr $ Map.toList names) ++
      blockOfLines "modules" (map pr $ Map.toList mods)
    where
      pr (x, y) = show x ++ " --> " ++ show y

instance Show AbstractName where
  show = show . anameName

instance Show AbstractModule where
  show = show . amodName

-- * Operations on names

instance HasRange AbstractName where
  getRange = getRange . anameName

instance SetRange AbstractName where
  setRange r x = x { anameName = setRange r $ anameName x }

-- * Operations on name and module maps.

mergeNames :: NamesInScope -> NamesInScope -> NamesInScope
mergeNames = Map.unionWith union

mergeModules :: ModulesInScope -> ModulesInScope -> ModulesInScope
mergeModules = Map.unionWith union

-- * Operations on name spaces

-- | The empty name space.
emptyNameSpace :: NameSpace
emptyNameSpace = NameSpace Map.empty Map.empty


-- | Map functions over the names and modules in a name space.
mapNameSpace :: (NamesInScope   -> NamesInScope  ) ->
		(ModulesInScope -> ModulesInScope) ->
		NameSpace -> NameSpace
mapNameSpace fd fm ns =
  ns { nsNames	 = fd $ nsNames ns
     , nsModules = fm $ nsModules  ns
     }

-- | Zip together two name spaces.
zipNameSpace :: (NamesInScope   -> NamesInScope   -> NamesInScope  ) ->
		(ModulesInScope -> ModulesInScope -> ModulesInScope) ->
		NameSpace -> NameSpace -> NameSpace
zipNameSpace fd fm ns1 ns2 =
  ns1 { nsNames	  = nsNames   ns1 `fd` nsNames   ns2
      , nsModules = nsModules ns1 `fm` nsModules ns2
      }

-- | Map monadic function over a namespace.
mapNameSpaceM :: Monad m => 
  (NamesInScope   -> m NamesInScope  ) ->
  (ModulesInScope -> m ModulesInScope) ->
  NameSpace -> m NameSpace
mapNameSpaceM fd fm ns = do
  ds <- fd $ nsNames ns
  ms <- fm $ nsModules ns
  return $ ns { nsNames = ds, nsModules = ms }

-- * General operations on scopes

-- | The empty scope.
emptyScope :: Scope
emptyScope = Scope { scopeName	  = noModuleName
		   , scopePublic  = emptyNameSpace
		   , scopePrivate = emptyNameSpace
		   }

-- | The empty scope info.
emptyScopeInfo :: ScopeInfo
emptyScopeInfo = ScopeInfo
		  { scopeStack	    = [emptyScope]
		  , scopeLocals	    = []
		  , scopePrecedence = TopCtx
		  }

-- | Map functions over the names and modules in a scope.
mapScope :: (Access -> NamesInScope   -> NamesInScope  ) ->
	    (Access -> ModulesInScope -> ModulesInScope) ->
	    Scope -> Scope
mapScope fd fm s =
  s { scopePrivate = mapNS PrivateAccess $ scopePrivate s
    , scopePublic  = mapNS PublicAccess  $ scopePublic  s
    }
  where
    mapNS acc = mapNameSpace (fd acc) (fm acc)

-- | Same as 'mapScope' but applies the same function to both the public and
--   private name spaces.
mapScope_ :: (NamesInScope   -> NamesInScope  ) ->
	     (ModulesInScope -> ModulesInScope) ->
	     Scope -> Scope
mapScope_ fd fm = mapScope (const fd) (const fm)

-- | Map monadic functions over the names and modules in a scope.
mapScopeM :: Monad m =>
  (Access -> NamesInScope   -> m NamesInScope  ) ->
  (Access -> ModulesInScope -> m ModulesInScope) ->
  Scope -> m Scope
mapScopeM fd fm s = do
  pri <- mapNS PrivateAccess $ scopePrivate s
  pub <- mapNS PublicAccess  $ scopePublic  s
  return $ s { scopePrivate = pri, scopePublic = pub }
  where
    mapNS acc = mapNameSpaceM (fd acc) (fm acc)

-- | Same as 'mapScopeM' but applies the same function to both the public and
--   private name spaces.
mapScopeM_ :: Monad m =>
  (NamesInScope   -> m NamesInScope  ) ->
  (ModulesInScope -> m ModulesInScope) ->
  Scope -> m Scope
mapScopeM_ fd fm = mapScopeM (const fd) (const fm)

-- | Zip together two scopes. The resulting scope has the same name as the
--   first scope.
zipScope :: (Access -> NamesInScope   -> NamesInScope   -> NamesInScope  ) ->
	    (Access -> ModulesInScope -> ModulesInScope -> ModulesInScope) ->
	    Scope -> Scope -> Scope
zipScope fd fm s1 s2 =
  s1 { scopePrivate = zipNS PrivateAccess (scopePrivate s1) (scopePrivate s2)
     , scopePublic  = zipNS PublicAccess  (scopePublic  s1) (scopePublic  s2)
     }
  where
    zipNS acc = zipNameSpace (fd acc) (fm acc)

-- | Same as 'zipScope' but applies the same function to both the public and
--   private name spaces.
zipScope_ :: (NamesInScope   -> NamesInScope   -> NamesInScope  ) ->
	     (ModulesInScope -> ModulesInScope -> ModulesInScope) ->
	     Scope -> Scope -> Scope
zipScope_ fd fm = zipScope (const fd) (const fm)

-- | Filter a scope keeping only concrete names matching the predicates.
--   The first predicate is applied to the names and the second to the modules.
filterScope :: (C.QName -> Bool) -> (C.QName -> Bool) -> Scope -> Scope
filterScope pd pm = mapScope_ (Map.filterKeys pd) (Map.filterKeys pm)

-- | Return all names in a scope, both public and private.
allNamesInScope :: Scope -> NamesInScope
allNamesInScope s = (mergeNames `on` nsNames) (scopePublic s) (scopePrivate s)

-- | Return all modules in a scope, both public and private.
allModulesInScope :: Scope -> ModulesInScope
allModulesInScope s = (mergeModules `on` nsModules) (scopePublic s) (scopePrivate s)

-- | Merge two scopes. The result has the name of the first scope.
mergeScope :: Scope -> Scope -> Scope
mergeScope = zipScope_ mergeNames mergeModules

-- | Merge a non-empty list of scopes. The result has the name of the first
--   scope in the list.
mergeScopes :: [Scope] -> Scope
mergeScopes [] = __IMPOSSIBLE__
mergeScopes ss = foldr1 mergeScope ss

-- * Specific operations on scopes

-- | Given a scope where all concrete names start with @M@, remove all the
--   @M@s. Used when opening a module @M@, in which case only those names
--   starting with @M@ are considered.
unqualifyScope :: C.QName -> Scope -> Scope
unqualifyScope m = mapScope_ unqual unqual
  where
    unqual = Map.mapKeys (unq m)

    unq _	     (C.QName _) = __IMPOSSIBLE__
    unq (C.Qual m n) (C.Qual m' q)
      | m == m'   = unq n q
      | otherwise = __IMPOSSIBLE__
    unq (C.QName m)  (C.Qual m' q)
      | m == m'	  = q
      | otherwise = __IMPOSSIBLE__

-- | Move all names in a scope to the public or private section, depending on
--   the first argument. Used when opening a module.
setScopeAccess :: Access -> Scope -> Scope
setScopeAccess a s = s { scopePublic  = pub
		       , scopePrivate = pri
		       }
  where
    one  = zipNameSpace mergeNames mergeModules (scopePublic s) (scopePrivate s)
    zero = emptyNameSpace

    (pub, pri) = case a of
      PublicAccess  -> (one, zero)
      PrivateAccess -> (zero, one)

-- | Add names to a scope.
addNamesToScope :: Access -> C.QName -> [AbstractName] -> Scope -> Scope
addNamesToScope acc x ys s = mergeScope s s1
  where
    s1 = setScopeAccess acc $ emptyScope
	 { scopePublic = emptyNameSpace { nsNames = Map.singleton x ys } }

-- | Add a name to a scope.
addNameToScope :: Access -> C.QName -> AbstractName -> Scope -> Scope
addNameToScope acc x y s = addNamesToScope acc x [y] s

-- | Add a module to a scope.
addModuleToScope :: Access -> C.QName -> AbstractModule -> Scope -> Scope
addModuleToScope acc x m s = mergeScope s s1
  where
    s1 = setScopeAccess acc $ emptyScope
	 { scopePublic = emptyNameSpace { nsModules = Map.singleton x [m] } }

-- | Apply an 'ImportDirective' to a scope.
applyImportDirective :: ImportDirective -> Scope -> Scope
applyImportDirective dir s = mergeScope usedOrHidden renamed
  where
    usedOrHidden = useOrHide (hideLHS (renaming dir) $ usingOrHiding dir) s
    renamed	 = rename (renaming dir) $ useOrHide useRenamedThings s

    useRenamedThings = Using $ map fst $ renaming dir

    hideLHS :: [(ImportedName, C.Name)] -> UsingOrHiding -> UsingOrHiding
    hideLHS _	i@(Using _) = i
    hideLHS ren (Hiding xs) = Hiding $ xs ++ map fst ren

    useOrHide :: UsingOrHiding -> Scope -> Scope
    useOrHide (Hiding xs) s = filterNames notElem notElem xs s
    useOrHide (Using  xs) s = filterNames elem	  elem	  xs s

    -- Qualified names are only ok if the top-most module is ok.
    okName pd pm (C.QName  x) = pd x
    okName pd pm (C.Qual m _) = pm m

    okModule pm (C.QName  x) = pm x
    okModule pm (C.Qual m _) = pm m

    filterNames :: (C.Name -> [C.Name] -> Bool) -> (C.Name -> [C.Name] -> Bool) ->
		   [ImportedName] -> Scope -> Scope
    filterNames pd pm xs = filterScope' (flip pd ds) (flip pm ms)
      where
	ds = [ x | ImportedName   x <- xs ]
	ms = [ m | ImportedModule m <- xs ]

    filterScope' pd pm = filterScope (okName pd pm) (okModule pm)

    -- Renaming
    rename :: [(ImportedName, C.Name)] -> Scope -> Scope
    rename rho = mapScope_ (Map.mapKeys $ renName drho mrho)
			   (Map.mapKeys $ renMod mrho)
      where
	mrho = [ (x, y) | (ImportedModule x, y) <- rho ]
	drho = [ (x, y) | (ImportedName	  x, y) <- rho ]

	ren r x = maybe x id $ lookup x r

	renName dr mr (C.QName  x) = C.QName $ ren dr x
	renName dr mr (C.Qual m x) = flip C.Qual x $ ren mr m

	renMod mr (C.QName  x) = C.QName $ ren mr x
	renMod mr (C.Qual m x) = flip C.Qual x $ ren mr m

-- | Rename the canical names in a scope.
renameCanonicalNames :: Map A.QName A.QName -> Map A.ModuleName A.ModuleName ->
			Scope -> Scope
renameCanonicalNames renD renM = mapScope_ renameD renameM
  where
    renameD = Map.map (map $ onName  rD)
    renameM = Map.map (map $ onMName rM)

    onName  f x = x { anameName = f $ anameName x }
    onMName f x = x { amodName  = f $ amodName  x }

    rD x = maybe x id $ Map.lookup x renD
    rM x = maybe x id $ Map.lookup x renM

-- * Inverse look-up

-- | Find the shortest concrete name that maps (uniquely) to a given abstract
--   name. Find defined names (first component of result) and module names
--   (second component) simultaneously.

-- | Takes the first component of 'inverseScopeLookup'.
inverseScopeLookupName :: A.QName -> ScopeInfo -> Maybe C.QName
inverseScopeLookupName x s = best $ invert x $ mergeScopes $ scopeStack s
  where
    len :: C.QName -> Int
    len (C.QName _)  = 1
    len (C.Qual _ x) = 1 + len x

    best xs = case sortBy (compare `on` len) xs of
      []    -> Nothing
      x : _ -> Just x

    invert x s = ds
      where
	ds = [ y | (y, zs) <- Map.toList $ allNamesInScope s
                 , x `elem` map anameName zs
                 , length zs == 1 || all ((==ConName) . anameKind) zs
             ]

-- | Takes the second component of 'inverseScopeLookup'.
inverseScopeLookupModule :: A.ModuleName -> ScopeInfo -> Maybe C.QName
inverseScopeLookupModule x s = best $ invert x $ mergeScopes $ scopeStack s
  where
    len :: C.QName -> Int
    len (C.QName _)  = 1
    len (C.Qual _ x) = 1 + len x

    best xs = case sortBy (compare `on` len) xs of
      []    -> Nothing
      x : _ -> Just x

    invert x s = ms
      where
	ms = [ y | (y, [m]) <- Map.toList $ allModulesInScope s, x == amodName m  ]


