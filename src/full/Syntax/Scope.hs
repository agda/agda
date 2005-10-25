{-# OPTIONS -fglasgow-exts #-}

{-| The scope analysis. Translates from concrete to abstract syntax.
-}
module Syntax.Scope where

import Control.Exception
import Control.Monad.Reader
import Data.Monoid
import Data.Typeable

import Syntax.Common
import Utils.Map
import Utils.Monad
import Utils.Maybe

{-

What should the scope analysis do? One option
would be to compute some of the name space stuff, making
all names fully qualified. How does this work for parameterised
modules? We keep namespace declarations and imports, but throw
away open declarations. We also remove all import directives.

module A (X : Set) where

  f = e
  g = .. f ..	-- what is the fully qualified name of f?

f -> A.f. In parameterised modules you get a name space with
the name of the module:

module A (X : Set) where
  namespace A = A X

module A where
  f = e
  namespace A' = A
  g = e'
  h = A' g -- is this valid? no. A' is a snapshot of A

Example name space maps

    import B, renaming (f to g)		-- B    : g -> B.f
    namespace B' = B, renaming (g to h)	-- B'   : h -> B.f
    open B', renaming (h to i)		-- local: i -> B.f

With parameterised modules

    import B		-- B/1 : f -> _
    namespace B' = B e	-- B'  : f -> B'.f

The treatment of namespace declarations differ in the two examples.
Solution: namespace declarations create new names so in the first example
B': h -> B'.h? We lose the connection to B, but this doesn't matter in scope
checking. We will have to repeat some of the work when type checking, but
probably not that much.

Argh? The current idea was to compute much of the scoping at this point,
simplifying the type checking. It might be the case that we would like to
know what is in scope (for interaction/plugins) at a particular program
point. Would we be able to do that with this approach? Yes. Question marks
and plugin calls get annotated with ScopeInfo.

Modules aren't first class, so in principle we could allow clashes between
module names and other names. The only place where we mix them is in import
directives. We could use the Haskell solution:

    open Foo, using (module Bar), renaming (module Q to Z)

What about exporting name spaces? I think it could be useful.
Simple solution: replace the namespace keyword with 'module':

  module Foo = Bar X, renaming (f to g)

Parameterised?

  module Foo (X : Set) = Bar X, renaming (f to g)?

Why not?

This way there the name space concept disappear. There are only modules.
This would be a Good Thing.

-}

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
		    , theName    :: QName
		    }

data KindOfName = FunName | ConName | DataName

data ResolvedNameSpace
	= ModuleName Arity NameSpace
	| UnknownModule

-- | The reason for this not being @Set Name@ is that we want
--   to know the position of the binding.
type LocalVariables = Map Name Name
type Modules	    = Map Name (Arity, NameSpace)
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
	    case lookupMap m $ modules ns of
		Nothing		-> throwDyn $ NoSuchModule m
		Just (0, ns')	-> res x emptyMap ns'
		Just (_, ns')	-> throwDyn $ UninstantiatedModule m

-- | Figure out what a qualified name refers to.
resolveName :: QName -> ScopeM ResolvedName
resolveName = resolve r
    where
	r vs ns x =
	    fromMaybe UnknownName $ mconcat
	    [ VarName <$> lookupMap x vs
	    , DefName <$> lookupMap x (definedNames ns)
	    ]

-- | In a pattern there are only two possibilities: either it's a constructor
--   or it's a variable. It's never undefined or a defined name.
resolvePatternName :: QName -> ScopeM ResolvedName
resolvePatternName = resolve r
    where
	r vs ns x =
	    case lookupMap x $ definedNames ns of
		Just c@(DefinedName ConName _)  -> DefName c
		_				-> VarName x

-- | Figure out what module a qualified name refers to.
resolveModule :: QName -> ScopeM ResolvedNameSpace
resolveModule = resolve r
    where
	r _ ns x = fromMaybe UnknownModule $
		    uncurry ModuleName <$> lookupMap x (modules ns)

{--------------------------------------------------------------------------
    Updating the scope
 --------------------------------------------------------------------------}

addModules :: Modules -> NameSpace -> NameSpace
addModules ms ns = ns { modules = modules ns `plusMap` ms }

addNames :: DefinedNames -> NameSpace -> NameSpace
addNames ds ns = ns { definedNames = definedNames ns `plusMap` ds }

addDef :: KindOfName -> Name -> ScopeInfo -> ScopeInfo
addDef k x si@ScopeInfo{currentNameSpace = ns} = si { currentNameSpace = ns' }
    where
	m   = moduleName ns
	qx  = DefinedName k (qualify m x)
	ns' = ns { definedNames = updateMap x qx (definedNames ns) }

addPrivate :: KindOfName -> Name -> ScopeInfo -> ScopeInfo
addPrivate k x si = si { privateNames = updateMap x qx $ privateNames si }
    where
	m   = moduleName $ currentNameSpace si
	qx  = DefinedName k (qualify m x)

-- | Assumes that the name of the @NameSpace@ is the right one (fully
--   qualified).
addModule :: Name -> Arity -> NameSpace -> ScopeInfo -> ScopeInfo
addModule x ar m si@ScopeInfo{currentNameSpace = ns} =
	si { currentNameSpace = ns' }
    where
	ns' = ns { modules = updateMap x (ar,m) $ modules ns }

addPrivateModule :: Name -> Arity -> NameSpace -> ScopeInfo -> ScopeInfo
addPrivateModule = undefined

addVar, remVar :: Name -> ScopeInfo -> ScopeInfo
addVar x si = si { localVariables = updateMap x x (localVariables si) }
remVar x si = si { localVariables = deleteMap x (localVariables si) }


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
	    VarName _	-> local (add k x . remVar x) cont
	    DefName y   -> throwDyn $ ClashingDefinition x (theName y)
    where
	add = case a of
		PrivateDecl -> addPrivate
		PublicDecl  -> addDef

{-| If a variable shadows a defined name we still keep the defined name.  The
    reason for this is in patterns, where constructors should take precedence
    over variables (and that it would be some work to remove the defined name).
-}
bindVariable :: Name -> ScopeM a -> ScopeM a
bindVariable x = local (addVar x)

defineModule :: Access -> Name -> Arity -> NameSpace -> ScopeM a -> ScopeM a
defineModule a x ar m cont =
    do	qx <- resolveModule $ QName x
	case qx of
	    UnknownModule   -> local (add x ar m) cont
	    ModuleName _ m' -> throwDyn $ ClashingModule x (moduleName m')
    where
	add = case a of
		PublicDecl  -> addModule
		PrivateDecl -> addPrivateModule

