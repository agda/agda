{-# OPTIONS -fglasgow-exts -cpp #-}

{-|

The scope analysis. Translates from concrete to abstract syntax.

-}
module Syntax.Scope where

import Control.Exception
import Control.Monad.Reader
import Control.Monad.State
import Data.Generics (Data,Typeable)
import Data.Monoid
import Data.Typeable
import Data.Map as Map
import Data.List as List
import Data.Tree

import Syntax.Position
import Syntax.Common
import Syntax.Concrete
import Syntax.Concrete.Name as CName
import Syntax.Abstract.Name as AName
import Syntax.Fixity
import qualified Syntax.Interface as I

import Utils.Monad
import Utils.Maybe
import Utils.Fresh

#include "../undefined.h"

---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | Exceptions thrown by the scope analysis.
data ScopeException
	= NotInScope CName.QName
	| NoSuchModule CName.QName
	| UninstantiatedModule CName.QName
	| ClashingDefinition CName.Name AName.QName
	| ClashingModule AName.ModuleName AName.ModuleName
	| ClashingImport CName.Name CName.Name
	| ClashingModuleImport CName.Name CName.Name
	| ModuleDoesntExport AName.ModuleName [ImportedName]
    deriving (Typeable, Show)

-- | A concrete name can be either a bound variable, a defined name (function,
--   constructor or datatype name) or unknown. 'resolve'ing a name gives you one
--   of these.
data ResolvedName
	= VarName AName.Name
	| DefName DefinedName
	| UnknownName
    deriving (Show)

-- | A defined name carries some extra information, such as whether it's private
--   or public and what fixity it has.
data DefinedName =
	DefinedName { access	 :: Access
		    , kindOfName :: KindOfName
		    , fixity :: Fixity
		    , theName    :: AName.QName
		    }
    deriving (Data,Typeable,Show)

{-| There are three kinds of defined names: function names, constructor names,
    and datatype names. It's probably a good idea to single out constructor
    names, but it's not clear that differentiating between function names and
    datatype names gives us anything. One could also imagining distinguishing
    between names of defined functions and names of postulates. One possible
    application of these fine-grained names is to have the interactive system
    color different kinds of names in pretty colors.

    At the moment we only distinguish between constructor names and other
    names, though.
-}
data KindOfName = FunName   -- ^ also includes datatypes
		| ConName
    deriving (Eq, Show,Typeable,Data)

-- | In addition to the names a module contains (which are stored in the
--   'NameSpace') we need to keep track of the arity of a module and whether
--   it is private or public.
data ModuleScope	=
	ModuleScope { moduleArity	:: Arity
		    , moduleAccess	:: Access
		    , moduleContents	:: NameSpace
		    }
    deriving (Show,Typeable,Data)

-- | When you 'resolveModule', this is what you get back.
data ResolvedModule
	= ModuleName ModuleScope
	| UnknownModule

-- | The value in the map is the binding occurence of a variable, so care should
--   be taken to update the 'Range' to the actual occurence. The 'Range' of the
--   binding occurence should be stored in the 'Syntax.Info.NameInfo'.
type LocalVariables = Map CName.Name AName.Name

type Modules	    = Map CName.Name ModuleScope
type DefinedNames   = Map CName.Name DefinedName

{-| A name space is a collection of names (defined names and module names). It
    also has a name of its own. The name is used when recomputing canonical
    names for implicit module declarations (which creates new names rather than
    new ways of referring to things). It is also used for error messages.
-}
data NameSpace =
	NSpace	{ moduleName	:: AName.ModuleName
		, definedNames	:: DefinedNames
		, modules	:: Modules
		}
    deriving (Data,Typeable,Show)

{-| The @privateNameSpace@ and the @publicNameSpace@ don't clash. The reason
    for separating the private and the public name space is that when we leave
    the current module we should pack it up in a 'ModuleScope' containing only
    the public stuff.

    Imported modules go in the private namespace since they aren't visible
    outside a module.

    We keep track of the @contextPrecedence@ for the holes. When inserting
    something into a hole we need to know whether it needs brackets or not.
-}
data ScopeInfo = ScopeInfo
	{ publicNameSpace   :: NameSpace
	, privateNameSpace  :: NameSpace
	, localVariables    :: LocalVariables
	, contextPrecedence :: Precedence
	}
   deriving (Data,Typeable)

-- | We need to generate fresh name ids when scope checking.
data ScopeState = ScopeState
	{ freshId   :: NameId
	}

-- | We need to go away and read interface files when scope checking an import
--   statement, so the scope monad must be an @IO@.
type ScopeM = StateT ScopeState (ReaderT ScopeInfo IO)


---------------------------------------------------------------------------
-- * Instances
---------------------------------------------------------------------------

instance HasRange DefinedName where
    getRange = getRange . theName

instance HasRange ScopeException where
    getRange (NotInScope x)		= getRange x
    getRange (ClashingImport x _)	= getRange x
    getRange (ClashingModuleImport x _) = getRange x
    getRange (NoSuchModule x)		= getRange x
    getRange (UninstantiatedModule x)	= getRange x
    getRange (ClashingModule x _)	= getRange x
    getRange (ClashingDefinition x _)	= getRange x
    getRange (ModuleDoesntExport _ xs)	= getRange xs

instance HasFresh NameId ScopeState where
    nextFresh s = (2 * i + 1, s { freshId = i + 1})
	where
	    i = freshId s

-- | Names generated by the scope monad have odd ids. Names generated by the
--   type checking monad should have even ids.
abstractName :: CName.Name -> ScopeM AName.Name
abstractName x =
    do	i <- fresh
	return $ AName.Name i x

---------------------------------------------------------------------------
-- * Exceptions
---------------------------------------------------------------------------

notInScope :: CName.QName -> a
notInScope x = throwDyn $ NotInScope x

clashingImport :: CName.Name -> CName.Name -> a
clashingImport x x' = throwDyn $ ClashingImport x x'

clashingModuleImport :: CName.Name -> CName.Name -> a
clashingModuleImport x x' = throwDyn $ ClashingModuleImport x x'

noSuchModule :: CName.QName -> a
noSuchModule x = throwDyn $ NoSuchModule x

uninstantiatedModule :: CName.QName -> a
uninstantiatedModule x = throwDyn $ UninstantiatedModule x

clashingModule :: AName.ModuleName -> AName.ModuleName -> a
clashingModule x y = throwDyn $ ClashingModule x y

clashingDefinition :: CName.Name -> AName.QName -> a
clashingDefinition x y = throwDyn $ ClashingDefinition x y

---------------------------------------------------------------------------
-- * Updating name spaces
---------------------------------------------------------------------------

-- | The names of the name spaces should be the same. Assumes there
--   are no clashes.
plusNameSpace :: NameSpace -> NameSpace -> NameSpace
plusNameSpace (NSpace name ds1 m1) (NSpace _ ds2 m2) =
	NSpace name (Map.unionWith __IMPOSSIBLE__ ds1 ds2)
		    (Map.unionWith __IMPOSSIBLE__ m1 m2)

-- | Same as 'plusNameSpace' but allows the modules to overlap.
plusNameSpace_ :: NameSpace -> NameSpace -> NameSpace
plusNameSpace_ (NSpace name ds1 m1) (NSpace _ ds2 m2) =
	NSpace name (Map.unionWith __IMPOSSIBLE__ ds1 ds2)
		    (Map.unionWith plusModules m1 m2)

-- | Merges to modules.
plusModules :: ModuleScope -> ModuleScope -> ModuleScope
plusModules mi1 mi2
    | moduleAccess mi1 /= moduleAccess mi2 || moduleArity mi1 /= moduleArity mi2
	= clashingModule (moduleName $ moduleContents mi1)
			 (moduleName $ moduleContents mi2)    -- TODO: different exception?
    | otherwise	= mi1 { moduleContents = moduleContents mi1 `plusNameSpace_`
					 moduleContents mi2
		      }

-- | Throws an exception if the name exists.
addName :: CName.Name -> DefinedName -> NameSpace -> NameSpace
addName x qx ns =
	ns { definedNames = Map.insertWithKey clash x qx $ definedNames ns }
    where
	clash x' _ _ = clashingImport x x'

addModule :: CName.Name -> ModuleScope -> NameSpace -> NameSpace
addModule x mi ns =
	ns { modules = Map.insertWithKey clash x mi $ modules ns }
    where
	clash x' _ _ = clashingModuleImport x x'

-- | Allows the module to already be defined. Used when adding modules
--   corresponding to directories (from imports).
addModule_ :: CName.Name -> ModuleScope -> NameSpace -> NameSpace
addModule_ x mi ns =
	ns { modules = Map.insertWithKey clash x mi $ modules ns }
    where
	clash x' mi mi' = plusModules mi mi'
	    -- TODO: we should only allow overlap of the pseudo-modules!

addQModule :: CName.QName -> ModuleScope -> NameSpace -> NameSpace
addQModule x mi ns = addQ [] x mi ns
    where
	addQ _  (CName.QName x)  mi ns = addModule x mi ns
	addQ ms (Qual m x) mi ns = addModule_ m mi' ns
	    where
		mi' = ModuleScope { moduleAccess   = PublicAccess
				  , moduleArity	   = 0
				  , moduleContents = addQ (ms ++ [m]) x mi
							  (emptyNameSpace $ mkQual ms m)
				  }
		mkQual ms x = mkModuleName $ foldr Qual (CName.QName x) ms
	next (CName.QName x)	= x
	next (Qual m x) = m

addModules :: [(CName.Name, ModuleScope)] -> NameSpace -> NameSpace
addModules ms ns = foldr (uncurry addModule) ns ms

addNames :: [(CName.Name, DefinedName)] -> NameSpace -> NameSpace
addNames ds ns	 = foldr (uncurry addName) ns ds

-- | Add the names from the first name space to the second. Throws an
--   exception on clashes.
addNameSpace :: NameSpace -> NameSpace -> NameSpace
addNameSpace ns0 ns =
    addNames (Map.assocs $ definedNames ns0)
    $ addModules (Map.assocs $ modules ns0) ns


-- | Recompute canonical names. All mappings will be @x -> M.x@ where
--   @M@ is the name of the name space. Recursively renames sub-modules.
makeFreshCanonicalNames :: NameSpace -> NameSpace
makeFreshCanonicalNames ns =
    ns { definedNames = Map.mapWithKey newName	 $ definedNames ns
       , modules      = Map.mapWithKey newModule $ modules ns
       }
    where
	m = moduleName ns
	newName x d = d { theName = (theName d) { qnameModule = m } }
	newModule x mi =
	    mi { moduleContents = makeFreshCanonicalNames
				  $ (moduleContents mi)
				    { moduleName = qualifyModule' m x }
	       }

emptyNameSpace :: AName.ModuleName -> NameSpace
emptyNameSpace x = NSpace { moduleName	 = x
			  , definedNames = Map.empty
			  , modules	 = Map.empty
			  }

---------------------------------------------------------------------------
-- * Updating the scope
---------------------------------------------------------------------------

updateNameSpace :: Access -> (NameSpace -> NameSpace) ->
		   ScopeInfo -> ScopeInfo
updateNameSpace PublicAccess f si =
    si { publicNameSpace = f $ publicNameSpace si }
updateNameSpace PrivateAccess f si =
    si { privateNameSpace = f $ privateNameSpace si }

defName :: Access -> KindOfName -> Fixity -> AName.Name ->
	   ScopeInfo -> ScopeInfo
defName a k fx x si = updateNameSpace a (addName (nameConcrete x) qx) si
    where
	m   = moduleName $ publicNameSpace si
	qx  = DefinedName a k fx (AName.qualify m x)

-- | Assumes that the name in the 'ModuleScope' fully qualified.
defModule :: CName.Name -> ModuleScope -> ScopeInfo -> ScopeInfo
defModule x mi = updateNameSpace (moduleAccess mi) f
    where
	f ns = ns { modules = Map.insert x mi $ modules ns }

bindVar, shadowVar :: AName.Name -> ScopeInfo -> ScopeInfo
bindVar x si	= si { localVariables = Map.insert (nameConcrete x) x (localVariables si) }
shadowVar x si	= si { localVariables = Map.delete (nameConcrete x)   (localVariables si) }

emptyScopeInfo :: AName.ModuleName -> ScopeInfo
emptyScopeInfo x = ScopeInfo { publicNameSpace	    = emptyNameSpace x
			     , privateNameSpace	    = emptyNameSpace x
			     , localVariables	    = Map.empty
			     , contextPrecedence    = TopCtx
			     }

emptyScopeInfo_ :: ScopeInfo
emptyScopeInfo_ = emptyScopeInfo $ mkModuleName $ CName.QName noName_

initScopeState :: ScopeState
initScopeState = ScopeState { freshId = 0 }

---------------------------------------------------------------------------
-- * Resolving names
---------------------------------------------------------------------------

setConcreteName :: CName.Name -> AName.Name -> AName.Name
setConcreteName c a = a { nameConcrete = c }

setConcreteQName :: CName.QName -> DefinedName -> DefinedName
setConcreteQName c d = d { theName = (theName d) { qnameConcrete = c } }

-- | Resolve a qualified name. Peals off name spaces until it gets
--   to an unqualified name and then applies the first argument.
resolve :: a -> (LocalVariables -> NameSpace -> CName.Name -> a) ->
	   CName.QName -> ScopeInfo -> a
resolve def f x si = res x vs (ns `plusNameSpace` ns')
    where
	vs  = localVariables si
	ns  = publicNameSpace si
	ns' = privateNameSpace si

	res (CName.QName x) vs ns = f vs ns x
	res (Qual m x) vs ns =
	    case Map.lookup m $ modules ns of
		Nothing			   -> def
		Just (ModuleScope 0 _ ns') -> res x empty ns'
		Just _			   -> uninstantiatedModule (CName.QName m)

-- | Figure out what a qualified name refers to.
resolveName :: CName.QName -> ScopeInfo -> ResolvedName
resolveName q = resolve UnknownName r q
    where
	r vs ns x =
	    fromMaybe UnknownName $ mconcat
	    [ VarName . setConcreteName x  <$> Map.lookup x vs
	    , DefName . setConcreteQName q <$> Map.lookup x (definedNames ns)
	    ]

-- | Monadic version of 'resolveName'.
resolveNameM :: CName.QName -> ScopeM ResolvedName
resolveNameM x = resolveName x <$> getScopeInfo

-- | This function doesn't bind 'VarName's, the caller has that responsibility.
resolvePatternNameM :: CName.QName -> ScopeM ResolvedName
resolvePatternNameM x =
    do	scope <- getScopeInfo
	resolve (return UnknownName) r x scope
    where
	r vs ns x =
	    case Map.lookup x $ definedNames ns of
		Just c@(DefinedName _ ConName _ _) -> return $ DefName c
		Just c@(DefinedName _ FunName _ _) -> return $ DefName c
		_   -> VarName <$> abstractName x

-- | Figure out what module a qualified name refers to.
resolveModule :: CName.QName -> ScopeInfo -> ResolvedModule
resolveModule = resolve UnknownModule r
    where
	r _ ns x = fromMaybe UnknownModule $
		    ModuleName <$> Map.lookup x (modules ns)


{--------------------------------------------------------------------------
    Wrappers for the resolve functions
 --------------------------------------------------------------------------}

-- | Make sure that a module hasn't been defined.
noModuleClash :: CName.QName -> ScopeM ()
noModuleClash x =
    do	si <- getScopeInfo
	case resolveModule x si of
	    UnknownModule   -> return ()
	    ModuleName m    -> clashingModule (mkModuleName x) $ moduleName $ moduleContents m

-- | Get the module referred to by a name. Throws an exception if the module
--   doesn't exist.
getModule :: CName.QName -> ScopeM ModuleScope
getModule x =
    do	si <- getScopeInfo
	case resolveModule x si of
	    UnknownModule   -> noSuchModule x
	    ModuleName m    -> return m

---------------------------------------------------------------------------
-- * Import directives
---------------------------------------------------------------------------

{-

Where should we check that the import directives are well-formed? I.e. that
    - you only refer to things that exist
    - you don't rename to something that's also imported
	using (x), renaming (y to x)
	renaming (y to x)   -- where x already exists
	hiding (x), renaming (y to x), should be ok though
Idea:
    - start with all names in the module
    - check that mentioned names exist
    - check that there are no internal clashes

import and open preserve canonical names
implicit modules create new canonical names

for implicit modules we can change the canonical names afterwards

-}

-- | Check that all names referred to in the import directive is exported by
--   the module.
invalidImportDirective :: NameSpace -> ImportDirective -> Maybe ScopeException
invalidImportDirective ns i =
    case badNames ++ badModules of
	[]  -> Nothing
	xs  -> Just $ ModuleDoesntExport (moduleName ns) xs
    where
	referredNames = names (usingOrHiding i) ++ List.map fst (renaming i)
	badNames    = [ x | x@(ImportedName x') <- referredNames
			  , Nothing <- [Map.lookup x' $ definedNames ns]
		      ]
	badModules  = [ x | x@(ImportedModule x') <- referredNames
			  , Nothing <- [Map.lookup x' $ modules ns]
		      ]

	names (Using xs)    = xs
	names (Hiding xs)   = xs

{-| Figure out how an import directive affects a name.

  - @applyDirective d x == Just y@, if @d@ contains a renaming @x to y@.

  - else @applyDirective d x == Just x@, if @d@ doesn't mention @x@ in a hiding clause and
    if @d@ has a @using@ clause, it mentions @x@.

  - @applyDirective d x == Nothing@, otherwise.

-}
applyDirective :: ImportDirective -> ImportedName -> Maybe CName.Name
applyDirective d x
    | renamed   = just_renamed
    | hidden    = Nothing
    | otherwise = Just $ importedName x
    where
        renamed      = isJust just_renamed
        just_renamed = List.lookup x (renaming d)
        hidden       =
            case usingOrHiding d of
                Hiding xs   ->    elem x xs
                Using  xs   -> notElem x xs

-- | Compute the imported names from a module. When importing canonical names doesn't
--   change. For instance, if the module @A@ contains a function @f@ and we say
--
--   > import A as B, renaming (f to g)
--
--   the canonical form of @B.g@ is @A.f@. Compare this to implicit module definitions
--   which creates new canonical names.
importedNames :: ModuleScope -> ImportDirective -> NameSpace
importedNames m i =
    case invalidImportDirective ns i of
	Just e	-> throwDyn e
	Nothing	-> addModules newModules $ addNames newNames $ emptyNameSpace name
    where
	name = moduleName ns
	ns = moduleContents m
	newNames = [ (x',qx)
		   | (x,qx)  <- Map.assocs (definedNames ns)
		   , Just x' <- [applyDirective i $ ImportedName x]
		   ]
	newModules = [ (x',m)
		     | (x,m)   <- Map.assocs (modules ns)
		     , Just x' <- [applyDirective i $ ImportedModule x]
		     ]

-- | Turn an interface to a module info structure. The main difference between
--   module interfaces and the module info structure is that submodules aren't
--   fully qualified in interface files.
interfaceToModule :: I.Interface -> ModuleScope
interfaceToModule i =
    ModuleScope	{ moduleAccess	    = PublicAccess
		, moduleArity	    = I.arity i
		, moduleContents    = mkNameSpace i
		}
    where
	mkNameSpace i =
	    NSpace
	    { moduleName    = name
	    , definedNames  =
		Map.fromList $
		       [ (nameConcrete x, mkName FunName fx x) | (x,fx) <- I.definedNames i ]
		    ++ [ (nameConcrete x, mkName ConName fx x) | (x,fx) <- I.constructorNames i ]
	    , modules	    =
		Map.fromList $ [ mkModule i' | i' <- I.subModules i ]
	    }
	    where
		name = I.moduleName i
		mkName k fx x =
		    DefinedName { access	= PublicAccess
				, kindOfName	= k
				, fixity	= fx
				, theName	= AName.qualify name x
				}
		mkModule i' = (x, interfaceToModule $ i' { I.moduleName = qx })
		    where
			MName [x] _ = I.moduleName i'
			qx = qualifyModule' name x


---------------------------------------------------------------------------
-- * Utility functions
---------------------------------------------------------------------------

-- | Get the current 'ScopeInfo'.
getScopeInfo :: ScopeM ScopeInfo
getScopeInfo = ask


-- | Get the name of the current module.
getCurrentModule :: ScopeM ModuleName
getCurrentModule = moduleName . publicNameSpace <$> getScopeInfo


-- | Get a function that returns the operator version of a name.
getFixityFunction :: ScopeM (CName.QName -> Fixity)
getFixityFunction =
    do	scope <- getScopeInfo
	return (f scope)
    where
	f scope x =
	    case resolveName x scope of
		VarName x   -> defaultFixity
		DefName d   -> fixity d
		_	    -> notInScope x

-- | Get the current (public) name space.
currentNameSpace :: ScopeM NameSpace
currentNameSpace = publicNameSpace <$> getScopeInfo

---------------------------------------------------------------------------
-- * Top-level functions
---------------------------------------------------------------------------

-- | Set the precedence of the current context. It's important to remember
--   to do this everywhere. It would be nice to have something that ensures
--   this.
setContext :: Precedence -> ScopeM a -> ScopeM a
setContext p =
    local $ \s -> s { contextPrecedence = p }

-- | Work inside the top-level module.
insideTopLevelModule :: CName.QName -> ScopeM a -> ScopeM a
insideTopLevelModule qx = local $ const $ emptyScopeInfo $ mkModuleName qx

-- | Work inside a module. This means moving everything in the
--   'publicNameSpace' to the 'privateNameSpace' and updating the names of
--   the both name spaces.
insideModule :: CName.Name -> ScopeM a -> ScopeM a
insideModule x = local upd
    where
	upd si = si { publicNameSpace = emptyNameSpace qx
		    , privateNameSpace = plusNameSpace pri pub
		    }
	    where
		pub = publicNameSpace si
		pri = (privateNameSpace si) { moduleName = qx }
		qx  = qualifyModule' (moduleName pub) x

-- | Add a defined name to the current scope.
defineName :: Access -> KindOfName -> Fixity -> CName.Name -> (AName.Name -> ScopeM a) -> ScopeM a
defineName a k f x cont = do
    si <- getScopeInfo
    case resolveName (CName.QName x) si of
	UnknownName -> do
	    x' <- abstractName x
	    local (defName a k f x') $ cont x'
	VarName _ -> do
	    x' <- abstractName x
	    local (defName a k f x' . shadowVar x') $ cont x'
	DefName y   -> clashingDefinition x (theName y)


{-| If a variable shadows a defined name we still keep the defined name.  The
    reason for this is in patterns, where constructors should take precedence
    over variables (and that it would be some work to remove the defined name).
-}
bindVariable :: AName.Name -> ScopeM a -> ScopeM a
bindVariable x = local (bindVar x)

-- | Bind multiple variables.
bindVariables :: [AName.Name] -> ScopeM a -> ScopeM a
bindVariables = foldr (.) id . List.map bindVariable

-- | Defining a module. For explicit modules this should be done after scope
--   checking the module.
defineModule :: CName.Name -> ModuleScope -> ScopeM a -> ScopeM a
defineModule x mi cont =
    do	noModuleClash (CName.QName x)
	local (defModule x mi) cont

-- | Opening a module.
openModule :: CName.QName -> ImportDirective -> ScopeM a -> ScopeM a
openModule x i cont =
    do	m <- getModule x
	let ns = importedNames m i
	local (updateNameSpace PrivateAccess
			       (addNameSpace ns)
	      ) cont

-- | Importing a module. The first argument is the name the module is imported
--   /as/. If there is no /as/ clause it should be the name of the module.
importModule :: CName.QName -> I.Interface -> ImportDirective -> ScopeM a -> ScopeM a
importModule x iface dir cont =
    do	noModuleClash x
	local ( updateNameSpace PrivateAccess
				(addQModule x m)
	      ) cont
    where
	m = interfaceToModule iface

-- | Implicit module declaration.
implicitModule :: CName.Name -> Access -> Arity -> CName.QName -> ImportDirective ->
		  ScopeM a -> ScopeM a
implicitModule x ac ar x' i cont =
    do	noModuleClash (CName.QName x)
	m    <- getModule x'
	this <- getCurrentModule
	let ns = makeFreshCanonicalNames $ 
		    (importedNames m i) { moduleName = AName.qualifyModule' this x }
	    m' = ModuleScope { moduleAccess   = ac
			     , moduleArity    = ar
			     , moduleContents = ns
			     }
	local (updateNameSpace ac (addModule x m')) cont

-- | Running the scope monad.
runScopeM :: ScopeState -> ScopeInfo -> ScopeM a -> IO a
runScopeM s i m =
	    flip runReaderT i
	    $ flip evalStateT s
	    $ m

runScopeM_ :: ScopeM a -> IO a
runScopeM_ = runScopeM initScopeState emptyScopeInfo_

---------------------------------------------------------------------------
-- * Debugging
---------------------------------------------------------------------------

scopeTree :: NameSpace -> Tree String
scopeTree ns =
    Node (show $ moduleName ns)
	 $  (List.map leaf $ Map.assocs $ definedNames ns)
	 ++ (List.map (scopeTree . moduleContents) $ Map.elems $ modules ns)
    where
	leaf (x,d) = Node (unwords [show x,"-->",show $ theName d]) []

instance Show ScopeInfo where
    show si =
	unlines [ "Public name space:"
		, drawTree $ scopeTree $ publicNameSpace si
		, "Private name space:"
		, drawTree $ scopeTree $ privateNameSpace si
		, "Local variables: " ++ show (localVariables si)
		, "Precedence: " ++ show (contextPrecedence si)
		]
