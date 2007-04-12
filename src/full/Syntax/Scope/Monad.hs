{-# OPTIONS_GHC -fglasgow-exts -cpp #-}

{-| The scope monad with operations.
-}

module Syntax.Scope.Monad where

import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map

import Syntax.Common
import Syntax.Position
import Syntax.Fixity
import Syntax.Abstract.Name as A
import Syntax.Concrete.Name as C
import Syntax.Concrete ( ImportDirective(publicOpen) )
import Syntax.Scope.Base

import TypeChecking.Monad.Base
import TypeChecking.Monad.State
import TypeChecking.Monad.Options

import Utils.Tuple
import Utils.Fresh

#include "../../undefined.h"

-- * The scope checking monad

-- | To simplify interaction between scope checking and type checking (in
--   particular when chasing imports), we use the same monad.
type ScopeM = TCM

-- * Errors

notInScope :: C.QName -> ScopeM a
notInScope x = typeError $ NotInScope [x]

-- * General operations

-- | Apply a function to the scope info.
modifyScopeInfo :: (ScopeInfo -> ScopeInfo) -> ScopeM ()
modifyScopeInfo f = do
  scope <- getScope
  setScope $ f scope

-- | Apply a function to the scope stack.
modifyScopeStack :: (ScopeStack -> ScopeStack) -> ScopeM ()
modifyScopeStack f = modifyScopeInfo $ \s -> s { scopeStack = f $ scopeStack s }

-- | Apply a function to the top scope.
modifyTopScope :: (Scope -> Scope) -> ScopeM ()
modifyTopScope f = modifyScopeStack $ \(s:ss) -> f s : ss

-- | Apply a function to the public or private name space.
modifyTopNameSpace :: Access -> (NameSpace -> NameSpace) -> ScopeM ()
modifyTopNameSpace acc f = modifyTopScope action
  where
    action s = s { scopePublic	= pub $ scopePublic  s
		 , scopePrivate = pri $ scopePrivate s
		 }
    (pub, pri) = case acc of
      PublicAccess  -> (f, id)
      PrivateAccess -> (id, f)

-- | Set context precedence
setContextPrecedence :: Precedence -> ScopeM ()
setContextPrecedence p = modifyScopeInfo $ \s -> s { scopePrecedence = p }

getContextPrecedence :: ScopeM Precedence
getContextPrecedence = scopePrecedence <$> getScope

withContextPrecedence :: Precedence -> ScopeM a -> ScopeM a
withContextPrecedence p m = do
  scope <- getScope
  withScope_ (scope { scopePrecedence = p }) m

-- * Names

-- | Create a fresh abstract name from a concrete name.
freshAbstractName :: C.Name -> ScopeM A.Name
freshAbstractName x = do
  i <- fresh
  return $ A.Name i x (getRange x)

-- * Simple queries

-- | Return the name of the current module.
getCurrentModule :: ScopeM ModuleName
getCurrentModule =
  A.qnameFromList . reverse . map scopeName . scopeStack <$> getScope

-- * Resolving names

data ResolvedName = VarName A.Name
		  | DefinedName AbstractName
		  | UnknownName

-- | Look up the abstract name referred to by a given concrete name.
resolveName :: C.QName -> ScopeM ResolvedName
resolveName x = do
  scope <- getScope
  let vars = map (C.QName -*- id) $ scopeLocals scope
      defs = allNamesInScope . mergeScopes . scopeStack $ scope
  case lookup x vars of
    Just y  -> return $ VarName $ setRange (getRange x) y
    Nothing -> case Map.lookup x defs of
      Just [d] -> return $ DefinedName $ setRange (getRange x) d
      Just ds  -> fail $ "ambiguous name: " ++ show (map anameName ds)	-- TODO!!
      Nothing  -> return UnknownName

-- | Look up a module in the scope.
resolveModule :: C.QName -> ScopeM AbstractModule
resolveModule x = do
  ms <- allModulesInScope . mergeScopes . scopeStack <$> getScope
  case Map.lookup x ms of
    Just [m] -> return $ setRange (getRange x) m
    Just []  -> __IMPOSSIBLE__
    Just ms  -> fail $ "ambiguous module: " ++ show x ++ ", " ++ show (map amodName ms)
    Nothing  -> fail $ "no such module: " ++ show x -- TODO!!

-- | Get the fixity of a name. The name is assumed to be in scope.
getFixity :: C.QName -> ScopeM Fixity
getFixity x = do
  r <- resolveName x
  case r of
    VarName _	  -> return defaultFixity
    DefinedName d -> return $ anameFixity d
    UnknownName	  -> __IMPOSSIBLE__

-- * Binding names

-- | Bind a variable. The abstract name is supplied as the second argument.
bindVariable :: C.Name -> A.Name -> ScopeM a -> ScopeM a
bindVariable x y ret = do
  scope <- getScope
  let scope' = scope { scopeLocals = (x, y) : scopeLocals scope }
  withScope_ scope' ret

-- | Bind a defined name.
bindName :: Access -> KindOfName -> Fixity -> C.Name -> ScopeM A.QName
bindName acc kind fx x = do
  m <- getCurrentModule
  y <- freshAbstractName x
  let d = A.qualify m y
  modifyTopScope $ addNameToScope acc (C.QName x) $ AbsName d kind fx
  return d

-- | Bind a module name.
bindModule :: Access -> Arity -> C.Name -> A.QName -> ScopeM ()
bindModule acc ar x m = bindQModule acc ar (C.QName x) m

-- | Bind a qualified module name.
bindQModule :: Access -> Arity -> C.QName -> A.QName -> ScopeM ()
bindQModule acc ar x m = do
  n <- length . scopeLocals <$> getScope
  modifyTopScope $ addModuleToScope acc x $ AbsModule m (ar + n)

-- * Module manipulation operations

-- | Push a new scope onto the scope stack
pushScope :: A.Name -> ScopeM ()
pushScope name = modifyScopeStack (s:)
  where
    s = emptyScope { scopeName = name }

{-| Pop the top scope from the scope stack and incorporate its (public)
    contents in the new top scope. Basically if the stack looks like this:

    @
    scope A: x -> Q.B.A.x
    scope B: y -> Q.B.y
    scope Q: ..
    @

    then after popping it will look like

    @
    scope B: A.x -> Q.B.A.x
	     y   -> Q.B.y
    scope Q: ..
-}
popScope :: ScopeM ()
popScope = do
  top <- getCurrentModule
  modifyScopeStack $ \(s0:s1:ss) ->
    mergeScope s1 (mapScope_ (qual s0) (qual s0) $ noPrivate s0) : ss
  where
    qual s m	= Map.mapKeys (C.Qual (nameConcrete $ scopeName s)) m
    noPrivate s = s { scopePrivate = emptyNameSpace }

-- | Returns a scope containing everything starting with a particular module
--   name. Used to open a module.
matchPrefix :: C.QName -> ScopeM Scope
matchPrefix m = filterScope (isPrefix m) (isPrefix m)
	      . mergeScopes . scopeStack <$> getScope
  where
    isPrefix _		   (C.QName _  ) = False
    isPrefix (C.QName m)   (C.Qual m' x) = m == m'
    isPrefix (C.Qual m m2) (C.Qual m' x) = m == m' && isPrefix m2 x

-- | Open a module. Assumes that all preconditions have been checked, i.e. that
--   the module is not opened into a different context than it was defined.
openModule_ :: C.QName -> ImportDirective -> ScopeM ()
openModule_ m dir =
  addScope . setScopeAccess acc
           . applyImportDirective dir
           . unqualifyScope m =<< matchPrefix m
  where
    addScope s = modifyTopScope (`mergeScope` s)
    acc | publicOpen dir  = PublicAccess
	| otherwise	  = PrivateAccess

