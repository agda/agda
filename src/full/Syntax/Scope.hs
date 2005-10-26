{-# OPTIONS -fglasgow-exts #-}

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

import Syntax.Common
import Syntax.Concrete

import Utils.Monad
import Utils.Maybe


{--------------------------------------------------------------------------
    Types
 --------------------------------------------------------------------------}

-- | Thrown by the scope analysis
data ScopeException
	= NotInScope QName
	| NoSuchModule Name
	| UninstantiatedModule Name
	| ClashingDefinition Name QName
	| ClashingModule Name QName
    deriving (Typeable)

data ResolvedName
	= VarName Name
	| DefName DefinedName
	| UnknownName

data DefinedName =
	DefinedName { kindOfName :: KindOfName
		    , access	 :: Access
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

{-| The @importedModules@, the @privateModules@ and the 'modules' of the
    @currentNameSpace@ don't clash. The @privateNames@ don't clash with the
    'definedNames' of the @currentNameSpace@. The reason for breaking out the
    private things and not store them in the name space is that they are only
    visible locally, so submodules never contain private things.

-}
data ScopeInfo = ScopeInfo
	{ currentNameSpace  :: NameSpace
	, importedModules   :: Modules
	, privateNames	    :: DefinedNames
	, privateModules    :: Modules
	, localVariables    :: LocalVariables
	}

type ScopeM = ReaderT ScopeInfo IO

{--------------------------------------------------------------------------
    Stuff
 --------------------------------------------------------------------------}

{--------------------------------------------------------------------------
    Resolving names
 --------------------------------------------------------------------------}

-- | Resolve a qualified name. Peals off name spaces until it gets
--   to an unqualified name and then applies the first argument.
resolve :: (LocalVariables -> NameSpace -> Name -> a) ->
	   QName -> ScopeM a
resolve f x =
    do	si <- ask
	let vs = localVariables si
	    im = importedModules si
	    pn = privateNames si
	    pm = privateModules si
	    ns = currentNameSpace si
	return $ res x vs (addNames pn $ foldr addModules ns [im, pm])
    where
	res (QName x) vs ns = f vs ns x
	res (Qual m x) vs ns =
	    case Map.lookup m $ modules ns of
		Nothing			    -> throwDyn $ NoSuchModule m
		Just (ModuleInfo 0 _ ns')   -> res x empty ns'
		Just _			    -> throwDyn $ UninstantiatedModule m

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
		Just c@(DefinedName _ ConName _) -> DefName c
		_				 -> VarName x

-- | Figure out what module a qualified name refers to.
resolveModule :: QName -> ScopeM ResolvedNameSpace
resolveModule = resolve r
    where
	r _ ns x = fromMaybe UnknownModule $
		    ModuleName <$> Map.lookup x (modules ns)

{--------------------------------------------------------------------------
    Updating the name spaces
 --------------------------------------------------------------------------}

addModules :: Modules -> NameSpace -> NameSpace
addModules ms ns = ns { modules = modules ns `Map.union` ms }

addNames :: DefinedNames -> NameSpace -> NameSpace
addNames ds ns = ns { definedNames = definedNames ns `Map.union` ds }

addName :: KindOfName -> Name -> NameSpace -> NameSpace
addName k x ns = ns { definedNames = updateMap x qx $ definedNames ns }
    where
	m   = moduleName ns
	qx  = DefinedName k PublicDecl (qualify m x)

addModule :: Name -> ModuleInfo -> NameSpace -> NameSpace
addModule x mi ns = ns { modules = Map.insert x mi $ modules ns }

{--------------------------------------------------------------------------
    Import directives
 --------------------------------------------------------------------------}

type NameFilter = ImportedName -> Maybe Name

filteredAddName :: NameFilter -> KindOfName -> Name -> NameSpace -> NameSpace
filteredAddName filtr k x ns =
    case filtr $ ImportedName x of
	Just x'	-> addName k x' ns
	_	-> ns

filteredAddModule :: NameFilter -> Name -> ModuleInfo -> NameSpace -> NameSpace
filteredAddModule filtr x mi ns =
    case filtr $ ImportedModule x of
	Just x'	-> addModule x' mi ns
	Nothing	-> ns

{--------------------------------------------------------------------------
    Updating the scope
 --------------------------------------------------------------------------}

defName :: KindOfName -> Name -> ScopeInfo -> ScopeInfo
defName k x si = si { currentNameSpace = addName (currentNameSpace si) }

defPrivate :: KindOfName -> Name -> ScopeInfo -> ScopeInfo
defPrivate k x si = si { privateNames = updateMap x qx $ privateNames si }
    where
	m   = moduleName $ currentNameSpace si
	qx  = DefinedName k PrivateDecl (qualify m x)

-- | Assumes that the name of the @NameSpace@ is the right one (fully
--   qualified).
defModule :: Name -> ModuleInfo -> ScopeInfo -> ScopeInfo
defModule x mi si@ScopeInfo{currentNameSpace = ns} =
	si { currentNameSpace = ns' }
    where
	f ns = ns { modules = Map.insert x mi $ modules ns }

defPrivateModule :: Name -> Arity -> NameSpace -> ScopeInfo -> ScopeInfo
defPrivateModule = undefined

bindVar, shadowVar :: Name -> ScopeInfo -> ScopeInfo
bindVar x si = si { localVariables = updateMap x x (localVariables si) }
shadowVar x si = si { localVariables = deleteMap x (localVariables si) }


{--------------------------------------------------------------------------
    Updating the scope monadically
 --------------------------------------------------------------------------}

{-| Add a defined name to the current scope. It should also add the name to the
    qualified versions of the current module:

    > module A where
    >   module B where
    >	  x   = e
    >     foo = x + B.x + A.B.x
-}
defineName :: Access -> KindOfName -> Name -> ScopeM a -> ScopeM a
defineName a k x cont =
    do	qx <- resolveName (QName x)
	case qx of
	    UnknownName	-> local (add k x) cont
	    VarName _	-> local (add k x . shadowVar x) cont
	    DefName y   -> throwDyn $ ClashingDefinition x (theName y)
    where
	add = case a of
		PrivateDecl -> defPrivate
		PublicDecl  -> defName

{-| If a variable shadows a defined name we still keep the defined name.  The
    reason for this is in patterns, where constructors should take precedence
    over variables (and that it would be some work to remove the defined name).
-}
bindVariable :: Name -> ScopeM a -> ScopeM a
bindVariable x = local (bindVar x)

defineModule :: Name -> ModuleInfo -> ScopeM a -> ScopeM a
defineModule x mi cont =
    do	qx <- resolveModule $ QName x
	case qx of
	    UnknownModule -> local (add x mi) cont
	    ModuleName m' -> throwDyn $ ClashingModule x
					    (moduleName $ moduleContents m')
    where
	add = case moduleAccess mi of
		PublicDecl  -> defModule
		PrivateDecl -> defPrivateModule

