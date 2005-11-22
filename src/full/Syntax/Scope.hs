{-# OPTIONS -fglasgow-exts -cpp #-}

{-|

The scope analysis. Translates from concrete to abstract syntax.

The discussion below is a transcript of my thinking process. This means that it
will contain things that were true (or I thought were true) at the time of
writing, but were later revised. For instance, it might say something like: the
canonical form of @x@ is @x@, and then later say that it is @A.x@.

What should the scope analysis do? One option
would be to compute some of the name space stuff, making
all names fully qualified. How does this work for parameterised
modules? We keep namespace declarations and imports, but throw
away open declarations. We also remove all import directives.

> module A (X : Set) where
> 
>   f = e
>   g = .. f ..	-- what is the fully qualified name of f?

@f -> A.f@. In parameterised modules you get a name space with
the name of the module:

> module A (X : Set) where
>   namespace A = A X

> module A where
>   f = e
>   namespace A' = A
>   g = e'
>   h = A' g -- is this valid? no. A' is a snapshot of A

Example name space maps

> import B, renaming (f to g)         -- B    : g -> B.f
> namespace B' = B, renaming (g to h) -- B'   : h -> B.f
> open B', renaming (h to i)          -- local: i -> B.f

With parameterised modules

> import B           -- B/1 : f -> _
> namespace B' = B e -- B'  : f -> B'.f

The treatment of namespace declarations differ in the two examples.
Solution: namespace declarations create new names so in the first example
@B': h -> B'.h@? We lose the connection to B, but this doesn't matter in scope
checking. We will have to repeat some of the work when type checking, but
probably not that much.

Argh? The current idea was to compute much of the scoping at this point,
simplifying the type checking. It might be the case that we would like to
know what is in scope (for interaction\/plugins) at a particular program
point. Would we be able to do that with this approach? Yes. Question marks
and plugin calls get annotated with ScopeInfo.

Modules aren't first class, so in principle we could allow clashes between
module names and other names. The only place where we mix them is in import
directives. We could use the Haskell solution:

> open Foo, using (module Bar), renaming (module Q to Z)

What about exporting name spaces? I think it could be useful.
Simple solution: replace the namespace keyword with 'module':

> module Foo = Bar X, renaming (f to g)

Parameterised?

> module Foo (X : Set) = Bar X, renaming (f to g)?

Why not?

This way there the name space concept disappear. There are only modules.
This would be a Good Thing.

Above it says that you can refer to the current module. What happens in this
example:

> module A where
>   module A where
>     module A where x = e
>     A.x -- which A? Current, parent or child?

Solution: don't allow references to the current or parent modules. A
similar problem crops up when a sibling module clashes with a child module:

> module Foo where
>   module A where x = e
>   module B where
>     module A where x = e'
>     A.x

In this case it is clear, however, that the child module shadows the
sibling. It would be nice if we could refer to the sibling module in some
way though. We can:

> module Foo where
>   module A where x = e
>   module B where
>     private module A' = A
>     module A where x = e'
>     A'.x

Conclusion: disallow referring to the current modules (modules are non-recursive).

What does the 'ScopeInfo' really contain? When you 'resolve' a name you should
get back the canonical version of that name. For instance:

> module A where
>   x = e
>   module B where
>     y = e'
>     -- x -> x, y -> y
>   -- B.y -> B.y
>   ...

What is the canonical form of a name? We would like to remove as much name juggling
as possible at this point.

Just because the user cannot refer to the current module doesn't mean that we shouldn't
be able to after scope analysis.

> module A where
>   x = e
>   module B where
>     y = e'
>     -- * x -> A.x
>     -- * y -> A.B.y
>   -- * B.y -> A.B.y
>   import B as B'
>   -- * B'.x -> B.x
>   import C
>   module CNat = C Nat
>   -- * CNat.x -> A.CNat.x

-}
module Syntax.Scope where

import Control.Exception
import Control.Monad.Reader
import Data.Monoid
import Data.Typeable
import Data.Map as Map
import Data.List as List

import Syntax.Common
import Syntax.Concrete
import qualified Syntax.Interface as I

import Utils.Monad
import Utils.Maybe

#include "../undefined.h"

{--------------------------------------------------------------------------
    Types
 --------------------------------------------------------------------------}

-- | Thrown by the scope analysis
data ScopeException
	= NotInScope QName
	| NoSuchModule QName
	| UninstantiatedModule QName
	| ClashingDefinition Name QName
	| ClashingModule QName QName
	| ClashingImport Name Name
	| ClashingModuleImport Name Name
	| ModuleDoesntExport QName [ImportedName]
    deriving (Typeable)

data ResolvedName
	= VarName Name
	| DefName DefinedName
	| UnknownName

data DefinedName =
	DefinedName { access	 :: Access
		    , kindOfName :: KindOfName
		    , fixity	 :: Fixity
		    , theName    :: QName
		    }

data ModuleInfo	=
	ModuleInfo  { moduleArity	:: Arity
		    , moduleAccess	:: Access
		    , moduleContents	:: NameSpace
		    }

data KindOfName = FunName | ConName | DataName

data ResolvedNameSpace
	= ModuleName ModuleInfo
	| UnknownModule

-- | The reason for this not being @Set Name@ is that we want
--   to know the position of the binding.
type LocalVariables = Map Name Name
type Modules	    = Map Name ModuleInfo
type DefinedNames   = Map Name DefinedName

data NameSpace =
	NSpace	{ moduleName	:: QName
		, definedNames	:: DefinedNames
		, modules	:: Modules
		}

{-| The @privateModules@ and the 'modules' of the @currentNameSpace@ don't
    clash. The @privateNames@ don't clash with the 'definedNames' of the
    @currentNameSpace@. The reason for breaking out the private things and not
    store them in the name space is that they are only visible locally, so
    submodules never contain private things.

    The @privateModules@ also contain imported modules.
-}
data ScopeInfo = ScopeInfo
	{ publicNameSpace   :: NameSpace
	, privateNameSpace  :: NameSpace
	, localVariables    :: LocalVariables
	, contextPrecedence :: Fixity
	}

type ScopeM = ReaderT ScopeInfo IO

{--------------------------------------------------------------------------
    Exceptions
 --------------------------------------------------------------------------}

notInScope x		    = throwDyn $ NotInScope x
clashingImport x x'	    = throwDyn $ ClashingImport x x'
clashingModuleImport x x'   = throwDyn $ ClashingModuleImport x x'
noSuchModule x		    = throwDyn $ NoSuchModule x
uninstantiatedModule x	    = throwDyn $ UninstantiatedModule x
clashingModule x y	    = throwDyn $ ClashingModule x y
clashingDefinition x y	    = throwDyn $ ClashingDefinition x y

{--------------------------------------------------------------------------
    Updating the name spaces
 --------------------------------------------------------------------------}

-- | The names of the name spaces should be the same. Assumes there
--   are no clashes.
plusNameSpace :: NameSpace -> NameSpace -> NameSpace
plusNameSpace (NSpace name ds1 m1) (NSpace _ ds2 m2) =
	NSpace name (Map.unionWith __UNDEFINED__ ds1 ds2)
		    (Map.unionWith __UNDEFINED__ m1 m2)

-- | Throws an exception if the name exists.
addName :: Name -> DefinedName -> NameSpace -> NameSpace
addName x qx ns =
	ns { definedNames = Map.insertWithKey clash x qx $ definedNames ns }
    where
	clash x' qx qx' = clashingImport x x'

addModule :: Name -> ModuleInfo -> NameSpace -> NameSpace
addModule x mi ns =
	ns { modules = Map.insertWithKey clash x mi $ modules ns }
    where
	clash x' qx qx' = clashingModuleImport x x'

addQModule :: QName -> ModuleInfo -> NameSpace -> NameSpace
addQModule (QName x) mi ns  = addModule x mi ns
addQModule (Qual m x) mi ns = addQModule x mi' ns
    where
	mi' = ModuleInfo { moduleAccess	    = PublicAccess
			 , moduleArity	    = 0
			 , moduleContents   =
			    NSpace { moduleName	    = QName m -- TODO: wrong
				   , definedNames   = Map.empty
				   , modules	    = Map.singleton (next x) mi
				   }
			 }
	next (QName x)	= x
	next (Qual m x) = m

addModules :: [(Name, ModuleInfo)] -> NameSpace -> NameSpace
addModules ms ns = foldr (uncurry addModule) ns ms

addNames :: [(Name, DefinedName)] -> NameSpace -> NameSpace
addNames ds ns	 = foldr (uncurry addName) ns ds

-- | Add the names from the first name space to the second. Throws an
--   exception on clashes.
addNameSpace :: NameSpace -> NameSpace -> NameSpace
addNameSpace ns0 ns =
    addNames (Map.assocs $ definedNames ns0)
    $ addModules (Map.assocs $ modules ns0) ns

{--------------------------------------------------------------------------
    Import directives
 --------------------------------------------------------------------------}

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

-- | Figure out how an import directive affects a name.
applyDirective :: ImportDirective -> ImportedName -> Maybe Name
applyDirective i x
    | Just x' <- renamed x  = Just x'
    | hidden x		    = Nothing
    | otherwise		    = Just $ importedName x
    where
	renamed x = List.lookup x (renaming i)
	hidden x =
	    case usingOrHiding i of
		Hiding xs   -> elem x xs
		Using xs    -> notElem x xs

-- | Compute the imported names from a module. Preserves canonical names.
importedNames :: ModuleInfo -> ImportDirective -> NameSpace
importedNames m i =
    case invalidImportDirective ns i of
	Just e	-> throwDyn e
	Nothing	-> addModules newModules $ addNames newNames ns
    where
	ns = moduleContents m
	newNames = [ (x',qx)
		   | (x,qx)  <- Map.assocs (definedNames ns)
		   , Just x' <- [applyDirective i $ ImportedName x]
		   ]
	newModules = [ (x',m)
		     | (x,m)   <- Map.assocs (modules ns)
		     , Just x' <- [applyDirective i $ ImportedModule x]
		     ]

-- | Recompute canonical names. All mappings will be @x -> M.x@ where
--   @M@ is the name of the name space. Recursively renames sub-modules.
makeFreshCanonicalNames :: NameSpace -> NameSpace
makeFreshCanonicalNames ns =
    ns { definedNames = Map.mapWithKey newName	 $ definedNames ns
       , modules      = Map.mapWithKey newModule $ modules ns
       }
    where
	m = moduleName ns
	newName x d = d { theName = qualify m x }
	newModule x mi =
	    mi { moduleContents = makeFreshCanonicalNames
				  $ (moduleContents mi)
				    { moduleName = qualify m x }
	       }

-- | Turn an interface to a module info structure.
interfaceToModule :: I.Interface -> ModuleInfo
interfaceToModule i =
    ModuleInfo	{ moduleAccess	    = PublicAccess
		, moduleArity	    = I.arity i
		, moduleContents    = mkNameSpace i
		}
    where
	mkNameSpace i =
	    NSpace
	    { moduleName    = name
	    , definedNames  =
		Map.fromList $
		       [ (x, mkName FunName f x)  | (x,f) <- I.definedNames i ]
		    ++ [ (x, mkName ConName f x)  | (x,f) <- I.constructorNames i ]
		    ++ [ (x, mkName DataName f x) | (x,f) <- I.datatypeNames i ]
	    , modules	    =
		Map.fromList $ [ mkModule i' | i' <- I.subModules i ]
	    }
	    where
		name = I.moduleName i
		mkName k f x =
		    DefinedName { access	= PublicAccess
				, kindOfName	= k
				, fixity	= f
				, theName	= qualify name x
				}
		mkModule i' = (x, interfaceToModule $ i { I.moduleName = qx })
		    where
			QName x = I.moduleName i'
			qx = qualify name x

{--------------------------------------------------------------------------
    Updating the scope
 --------------------------------------------------------------------------}

updateNameSpace :: Access -> (NameSpace -> NameSpace) ->
		   ScopeInfo -> ScopeInfo
updateNameSpace PublicAccess f si =
    si { publicNameSpace = f $ publicNameSpace si }
updateNameSpace PrivateAccess f si =
    si { privateNameSpace = f $ privateNameSpace si }

defName :: Access -> KindOfName -> Fixity -> Name -> ScopeInfo -> ScopeInfo
defName a k f x si = updateNameSpace a (addName x qx) si
    where
	m   = moduleName $ publicNameSpace si
	qx  = DefinedName a k f (qualify m x)

-- | Assumes that the name in the 'ModuleInfo' fully qualified.
defModule :: Name -> ModuleInfo -> ScopeInfo -> ScopeInfo
defModule x mi = updateNameSpace (moduleAccess mi) f
    where
	f ns = ns { modules = Map.insert x mi $ modules ns }

bindVar, shadowVar :: Name -> ScopeInfo -> ScopeInfo
bindVar x si	= si { localVariables = Map.insert x x (localVariables si) }
shadowVar x si	= si { localVariables = Map.delete x (localVariables si) }


{--------------------------------------------------------------------------
    Resolving names
 --------------------------------------------------------------------------}

-- | Resolve a qualified name. Peals off name spaces until it gets
--   to an unqualified name and then applies the first argument.
resolve :: (LocalVariables -> NameSpace -> Name -> a) ->
	   QName -> ScopeM a
resolve f x =
    do	si <- ask
	let vs	= localVariables si
	    ns	= publicNameSpace si
	    ns'	= privateNameSpace si
	return $ res x vs (ns `plusNameSpace` ns')
    where
	res (QName x) vs ns = f vs ns x
	res (Qual m x) vs ns =
	    case Map.lookup m $ modules ns of
		Nothing			    -> noSuchModule (QName m)
		Just (ModuleInfo 0 _ ns')   -> res x empty ns'
		Just _			    -> uninstantiatedModule (QName m)

-- | Figure out what a qualified name refers to.
resolveName :: QName -> ScopeM ResolvedName
resolveName = resolve r
    where
	r vs ns x =
	    fromMaybe UnknownName $ mconcat
	    [ VarName <$> Map.lookup x vs
	    , DefName <$> Map.lookup x (definedNames ns)
	    ]

-- | In a pattern there are only two possibilities: either it's a constructor
--   or it's a variable. It's never undefined or a defined name.
resolvePatternName :: QName -> ScopeM ResolvedName
resolvePatternName = resolve r
    where
	r vs ns x =
	    case Map.lookup x $ definedNames ns of
		Just c@(DefinedName _ ConName _ _)  -> DefName c
		_				    -> VarName x

-- | Figure out what module a qualified name refers to.
resolveModule :: QName -> ScopeM ResolvedNameSpace
resolveModule = resolve r
    where
	r _ ns x = fromMaybe UnknownModule $
		    ModuleName <$> Map.lookup x (modules ns)


{--------------------------------------------------------------------------
    Wrappers for the resolve functions
 --------------------------------------------------------------------------}

-- | Make sure that a module hasn't been defined.
noModuleClash :: QName -> ScopeM ()
noModuleClash x =
    do	qx <- resolveModule x
	case qx of
	    UnknownModule   -> return ()
	    ModuleName m    -> clashingModule x $ moduleName $ moduleContents m

-- | Get the module referred to by a name. Throws an exception if the module
--   doesn't exist.
getModule :: QName -> ScopeM ModuleInfo
getModule x =
    do	qx <- resolveModule x
	case qx of
	    UnknownModule   -> noSuchModule x
	    ModuleName m    -> return m

{--------------------------------------------------------------------------
    Updating the scope monadically
 --------------------------------------------------------------------------}

-- | Add a defined name to the current scope.
defineName :: Access -> KindOfName -> Fixity -> Name -> ScopeM a -> ScopeM a
defineName a k f x cont =
    do	qx <- resolveName (QName x)
	case qx of
	    UnknownName	-> local (defName a k f x) cont
	    VarName _	-> local (defName a k f x . shadowVar x) cont
	    DefName y   -> clashingDefinition x (theName y)


{-| If a variable shadows a defined name we still keep the defined name.  The
    reason for this is in patterns, where constructors should take precedence
    over variables (and that it would be some work to remove the defined name).
-}
bindVariable :: Name -> ScopeM a -> ScopeM a
bindVariable x = local (bindVar x)

-- | Defining a module. For explicit modules this should be done after scope
--   checking the module.
defineModule :: Name -> ModuleInfo -> ScopeM a -> ScopeM a
defineModule x mi cont =
    do	noModuleClash (QName x)
	local (defModule x mi) cont

-- | Opening a module.
openModule :: QName -> ImportDirective -> ScopeM a -> ScopeM a
openModule x i cont =
    do	m <- getModule x
	let ns = importedNames m i
	local (updateNameSpace PrivateAccess
			       (addNameSpace ns)
	      ) cont

-- | Importing a module. The first argument is the name the module is imported
--   /as/. If there is no /as/ clause it should be the name of the module.
importModule :: QName -> I.Interface -> ImportDirective -> ScopeM a -> ScopeM a
importModule x iface dir cont =
    do	noModuleClash x
	local ( updateNameSpace PrivateAccess
				(addQModule x m)
	      ) cont
    where
	m = interfaceToModule iface

-- | Implicit module declaration.
implicitModule :: Name -> Access -> Arity -> QName -> ImportDirective ->
		  ScopeM a -> ScopeM a
implicitModule x ac ar x' i cont =
    do	noModuleClash (QName x)
	m <- getModule x'
	let ns = makeFreshCanonicalNames $ importedNames m i
	local (updateNameSpace ac (addNameSpace ns)) cont

