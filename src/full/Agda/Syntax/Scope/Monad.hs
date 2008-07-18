{-# OPTIONS_GHC -fglasgow-exts -cpp #-}

{-| The scope monad with operations.
-}

module Agda.Syntax.Scope.Monad where

import Prelude hiding (mapM)
import Control.Applicative
import Control.Monad hiding (mapM)
import Data.Map (Map)
import Data.Traversable
import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Concrete as C
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Options

import Agda.Utils.Tuple
import Agda.Utils.Fresh
import Agda.Utils.Size
import Agda.Utils.List

#include "../../undefined.h"
import Agda.Utils.Impossible

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

-- | Apply a monadic function to the top scope.
modifyTopScopeM :: (Scope -> ScopeM Scope) -> ScopeM ()
modifyTopScopeM f = do
  s : _ <- scopeStack <$> getScope
  s'	<- f s
  modifyTopScope (const s')

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
  p' <- getContextPrecedence
  setContextPrecedence p
  x <- m
  setContextPrecedence p'
  return x

getLocalVars :: ScopeM LocalVars
getLocalVars = scopeLocals <$> getScope

setLocalVars :: LocalVars -> ScopeM ()
setLocalVars vars = modifyScope $ \s -> s { scopeLocals = vars }

-- | Run a computation without changing the local variables.
withLocalVars :: ScopeM a -> ScopeM a
withLocalVars m = do
  vars <- getLocalVars
  x    <- m
  setLocalVars vars
  return x

-- * Names

-- | Create a fresh abstract name from a concrete name.
freshAbstractName :: Fixity -> C.Name -> ScopeM A.Name
freshAbstractName fx x = do
  i <- fresh
  return $ A.Name i x (getRange x) fx

-- | @freshAbstractName_ = freshAbstractName defaultFixity@
freshAbstractName_ :: C.Name -> ScopeM A.Name
freshAbstractName_ = freshAbstractName defaultFixity

-- | Create a fresh abstract qualified name.
freshAbstractQName :: Fixity -> C.Name -> ScopeM A.QName
freshAbstractQName fx x = do
  y <- freshAbstractName fx x
  m <- getCurrentModule
  return $ A.qualify m y

-- * Simple queries

-- | Return the name of the current module.
getCurrentModule :: ScopeM ModuleName
getCurrentModule =
  A.mnameFromList . concatMap A.mnameToList . reverse . map scopeName . scopeStack <$> getScope

-- * Resolving names

data ResolvedName = VarName A.Name
		  | DefinedName AbstractName
                  | ConstructorName [AbstractName]
		  | UnknownName
  deriving (Show)

-- | Look up the abstract name referred to by a given concrete name.
resolveName :: C.QName -> ScopeM ResolvedName
resolveName x = do
  scope <- getScope
  let vars = map (C.QName -*- id) $ scopeLocals scope
      defs = allNamesInScope . mergeScopes . scopeStack $ scope
  case lookup x vars of
    Just y  -> return $ VarName $ y { nameConcrete = unqualify x }
    Nothing -> case Map.lookup x defs of
      Just ds | all ((==ConName) . anameKind) ds ->
        return $ ConstructorName
               $ map (\d -> updateConcreteName d $ unqualify x) ds
      Just [d] -> return $ DefinedName $ updateConcreteName d (unqualify x)
      Just ds  -> typeError $ AmbiguousName x (map anameName ds)
      Nothing  -> return UnknownName
  where
  updateConcreteName :: AbstractName -> C.Name -> AbstractName
  updateConcreteName d@(AbsName { anameName = an@(A.QName { qnameName = qn }) }) x =
    d { anameName = an { qnameName = qn { nameConcrete = x } } }

-- | Look up a module in the scope.
resolveModule :: C.QName -> ScopeM AbstractModule
resolveModule x = do
  ms <- resolveModule' x
  case ms of
    [m] -> return $ updateRange m x
    []  -> typeError $ NoSuchModule x
    ms  -> typeError $ AmbiguousModule x (map amodName ms)
  where
  -- Sets the ranges of name parts present in the concrete name to
  -- those used in that name, and sets other ranges to 'noRange'.
  updateRange :: AbstractModule -> C.QName -> AbstractModule
  updateRange (AbsModule (MName ms)) x = AbsModule $ MName $
    reverse $ zipWith setRange
                      (reverse (map getRange $ qnameParts x)
                       ++ repeat noRange)
                      (reverse ms)

resolveModule' :: C.QName -> ScopeM [AbstractModule]
resolveModule' x = do
  ms <- allModulesInScope . mergeScopes . scopeStack <$> getScope
  case Map.lookup x ms of
    Just ms -> return ms
    Nothing -> return []

-- | Get the fixity of a name. The name is assumed to be in scope.
getFixity :: C.QName -> ScopeM Fixity
getFixity x = do
  r <- resolveName x
  case r of
    VarName y          -> return $ nameFixity y
    DefinedName d      -> return $ nameFixity $ qnameName $ anameName d
    ConstructorName ds
      | allEqual fs    -> return $ head fs
      | otherwise      -> return defaultFixity
      where
        fs = map (nameFixity . qnameName . anameName) ds
    UnknownName        -> __IMPOSSIBLE__

-- * Binding names

-- | Bind a variable. The abstract name is supplied as the second argument.
bindVariable :: C.Name -> A.Name -> ScopeM ()
bindVariable x y = do
  scope <- getScope
  let scope' = scope { scopeLocals = (x, y) : scopeLocals scope }
  setScope scope'

-- | Bind a defined name. Must not shadow anything.
bindName :: Access -> KindOfName -> C.Name -> A.QName -> ScopeM ()
bindName acc kind x y = do
  r  <- resolveName (C.QName x)
  ys <- case r of
    DefinedName	d      -> typeError $ ClashingDefinition x $ anameName d
    VarName z          -> typeError $ ClashingDefinition x $ A.qualify (mnameFromList []) z
    ConstructorName ds
      | kind == ConName && all ((==ConName) . anameKind) ds -> return [ AbsName y kind ]
      | otherwise -> typeError $ ClashingDefinition x $ anameName (head ds) -- TODO: head
    UnknownName        -> return [AbsName y kind]
  modifyTopScope $ addNamesToScope acc (C.QName x) ys

-- | Bind a module name.
bindModule :: Access -> C.Name -> A.ModuleName -> ScopeM ()
bindModule acc x m = bindQModule acc (C.QName x) m

-- | Bind a qualified module name.
bindQModule :: Access -> C.QName -> A.ModuleName -> ScopeM ()
bindQModule acc x m = modifyTopScope $ addModuleToScope acc x $ AbsModule m

-- * Module manipulation operations

-- | Clear the scope of any no names.
stripNoNames :: ScopeM ()
stripNoNames = modifyScopeStack $ map strip
  where
    strip     = mapScope (\_ -> stripN) (\_ -> stripN)
    stripN m  = Map.filterWithKey (const . notNoName) m
    notNoName = not . any isNoName . qnameParts

-- | Push a new scope onto the scope stack
pushScope :: A.ModuleName -> ScopeM ()
pushScope name = modifyScopeStack (s:)
  where
    s = emptyScope { scopeName = name }

{-| Pop the top scope from the scope stack and incorporate its (public)
    contents in the new top scope. Depending on the first argument the contents
    is added to the public or private part of the top scope. Basically if the
    stack looks like this:

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
    @
-}
popScope :: Access -> ScopeM ()
popScope acc = do
  top <- getCurrentModule
  modifyScopeStack $ \(s0:s1:ss) ->
    mergeScope s1 (setScopeAccess acc $ mapScope_ (qual s0) (qual s0) $ noPrivate s0) : ss
  where
    qual s m	= Map.mapKeys (qual' (mnameToList $ scopeName s)) m
      where
	qual' xs x = foldr C.Qual x $ map nameConcrete xs
    noPrivate s = s { scopePrivate = emptyNameSpace }

-- | Pop the top scope from the stack and discard its contents.
popScope_ :: ScopeM ()
popScope_ = modifyScopeStack tail

-- | Returns a scope containing everything starting with a particular module
--   name. Used to open a module.
matchPrefix :: C.QName -> ScopeM Scope
matchPrefix m = filterScope (isPrefix m) (isPrefix m)
	      . mergeScopes . scopeStack <$> getScope
  where
    isPrefix _		   (C.QName _  ) = False
    isPrefix (C.QName m)   (C.Qual m' x) = m == m'
    isPrefix (C.Qual m m2) (C.Qual m' x) = m == m' && isPrefix m2 x

-- | @renamedCanonicalNames old new s@ returns a renaming replacing all
--   (abstract) names @old.m.x@ with @new.m.x@. Any other names are left
--   untouched.
renamedCanonicalNames :: ModuleName -> ModuleName -> Scope ->
		       ScopeM (Map A.QName A.QName, Map A.ModuleName A.ModuleName)
renamedCanonicalNames old new s = (,) <$> renamedNames names <*> renamedMods mods
  where
    ns	  = scopePublic $ setScopeAccess PublicAccess s
    names = nsNames ns
    mods  = nsModules ns

    renamedNames ds = Map.fromList <$> zip xs <$> mapM renName xs
      where
	xs = filter (`isInModule` old) $ map anameName $ concat $ Map.elems ds

    renamedMods ms = Map.fromList <$> zip xs <$> mapM renMod xs
      where
	xs = filter (`isSubModuleOf` old) $ map amodName $ concat $ Map.elems ms

    -- Change a binding M.x -> old.M'.y to M.x -> new.M'.y
    renName :: A.QName -> ScopeM A.QName
    renName y = do
      i <- fresh
      return . qualifyQ new . dequalify
	     $ y { qnameName = (qnameName y) { nameId = i } }
      where
	dequalify = A.qnameFromList . drop (size old) . A.qnameToList

    -- Change a binding M.x -> old.M'.y to M.x -> new.M'.y
    renMod :: A.ModuleName -> ScopeM A.ModuleName
    renMod = return . qualifyM new . dequalify
      where
	dequalify = A.mnameFromList . drop (size old) . A.mnameToList

-- | Apply an importdirective and check that all the names mentioned actually
--   exist.
applyImportDirectiveM :: C.QName -> ImportDirective -> Scope -> ScopeM Scope
applyImportDirectiveM m dir scope = do
  xs <- filterM doesn'tExist names
  reportLn 20 $ "non existing names: " ++ show xs
  case xs of
    []	-> return $ applyImportDirective dir scope
    _	-> typeError $ ModuleDoesntExport m xs
  where
    names :: [ImportedName]
    names = map fst (renaming dir) ++ case usingOrHiding dir of
      Using  xs -> xs
      Hiding xs -> xs

    doesn'tExist (ImportedName x) =
      case Map.lookup (C.QName x) $ allNamesInScope scope of
	Just _	-> return False
	Nothing	-> return True
    doesn'tExist (ImportedModule x) =
      case Map.lookup (C.QName x) $ allModulesInScope scope of
	Just _	-> return False
	Nothing	-> return True

-- | Open a module. Assumes that all preconditions have been checked, i.e. that
--   the module is not opened into a different context than it was defined.
openModule_ :: C.QName -> ImportDirective -> ScopeM ()
openModule_ m dir =
  addScope  .  setScopeAccess acc
           =<< applyImportDirectiveM m dir
            .  unqualifyScope m =<< matchPrefix m
  where
    addScope s = modifyTopScope (`mergeScope` s)
    acc | publicOpen dir  = PublicAccess
	| otherwise	  = PrivateAccess

