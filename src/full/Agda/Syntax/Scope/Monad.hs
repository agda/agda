{-# LANGUAGE CPP #-}

{-| The scope monad with operations.
-}

module Agda.Syntax.Scope.Monad where

import Prelude hiding (mapM)
import Control.Arrow ((***), first, second)
import Control.Applicative
import Control.Monad hiding (mapM)
import Control.Monad.Writer hiding (mapM)
import Control.Monad.State hiding (mapM)

import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Concrete as C
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Options

import qualified Agda.Utils.AssocList as AssocList
import Agda.Utils.Fresh
import Agda.Utils.Function
import Agda.Utils.List
import Agda.Utils.Null (unlessNull)
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "../../undefined.h"
import Agda.Utils.Impossible

-- * The scope checking monad

-- | To simplify interaction between scope checking and type checking (in
--   particular when chasing imports), we use the same monad.
type ScopeM = TCM

-- * Errors

isDatatypeModule :: A.ModuleName -> ScopeM Bool
isDatatypeModule m = do
   sc <- getScope
   return $ maybe __IMPOSSIBLE__ scopeDatatypeModule (Map.lookup m (scopeModules sc))

-- * General operations

getCurrentModule :: ScopeM A.ModuleName
getCurrentModule = setRange noRange . scopeCurrent <$> getScope

setCurrentModule :: A.ModuleName -> ScopeM ()
setCurrentModule m = modifyScopeInfo $ \s -> s { scopeCurrent = m }

withCurrentModule :: A.ModuleName -> ScopeM a -> ScopeM a
withCurrentModule new action = do
  old <- getCurrentModule
  setCurrentModule new
  x   <- action
  setCurrentModule old
  return x

withCurrentModule' :: (MonadTrans t, Monad (t ScopeM)) => A.ModuleName -> t ScopeM a -> t ScopeM a
withCurrentModule' new action = do
  old <- lift getCurrentModule
  lift $ setCurrentModule new
  x   <- action
  lift $ setCurrentModule old
  return x

getNamedScope :: A.ModuleName -> ScopeM Scope
getNamedScope m = do
  scope <- getScope
  case Map.lookup m (scopeModules scope) of
    Just s  -> return s
    Nothing -> do
      reportSLn "" 0 $ "ERROR: In scope\n" ++ show scope ++ "\nNO SUCH SCOPE " ++ show m
      __IMPOSSIBLE__

getCurrentScope :: ScopeM Scope
getCurrentScope = getNamedScope =<< getCurrentModule

-- | Create a new module with an empty scope (Bool is True if it is a datatype module)
createModule :: Bool -> A.ModuleName -> ScopeM ()
createModule b m = do
  s <- getCurrentScope
  let parents = scopeName s : scopeParents s
  modifyScopes $ Map.insert m emptyScope { scopeName           = m
                                         , scopeParents        = parents
                                         , scopeDatatypeModule = b }

-- | Apply a function to the scope info.
modifyScopeInfo :: (ScopeInfo -> ScopeInfo) -> ScopeM ()
modifyScopeInfo = modifyScope

-- | Apply a function to the scope map.
modifyScopes :: (Map A.ModuleName Scope -> Map A.ModuleName Scope) -> ScopeM ()
modifyScopes f = modifyScopeInfo $ \s -> s { scopeModules = f $ scopeModules s }

-- | Apply a function to the given scope.
modifyNamedScope :: A.ModuleName -> (Scope -> Scope) -> ScopeM ()
modifyNamedScope m f = modifyScopes $ Map.adjust f m

setNamedScope :: A.ModuleName -> Scope -> ScopeM ()
setNamedScope m s = modifyNamedScope m $ const s

-- | Apply a monadic function to the top scope.
modifyNamedScopeM :: A.ModuleName -> (Scope -> ScopeM Scope) -> ScopeM ()
modifyNamedScopeM m f = setNamedScope m =<< f =<< getNamedScope m

-- | Apply a function to the current scope.
modifyCurrentScope :: (Scope -> Scope) -> ScopeM ()
modifyCurrentScope f = getCurrentModule >>= (`modifyNamedScope` f)

modifyCurrentScopeM :: (Scope -> ScopeM Scope) -> ScopeM ()
modifyCurrentScopeM f = getCurrentModule >>= (`modifyNamedScopeM` f)

-- | Apply a function to the public or private name space.
modifyCurrentNameSpace :: NameSpaceId -> (NameSpace -> NameSpace) -> ScopeM ()
modifyCurrentNameSpace acc f = modifyCurrentScope $ updateScopeNameSpaces $
  AssocList.updateAt acc f

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

modifyLocalVars :: (LocalVars -> LocalVars) -> ScopeM ()
modifyLocalVars = modifyScope . updateScopeLocals

setLocalVars :: LocalVars -> ScopeM ()
setLocalVars vars = modifyLocalVars $ const vars

-- | Run a computation without changing the local variables.
withLocalVars :: ScopeM a -> ScopeM a
withLocalVars m = do
  vars <- getLocalVars
  x    <- m
  setLocalVars vars
  return x

-- * Names

-- | Create a fresh abstract name from a concrete name.
--
--   This function is used when we translate a concrete name
--   in a binder.  The 'Range' of the concrete name is
--   saved as the 'nameBindingSite' of the abstract name.
freshAbstractName :: Fixity' -> C.Name -> ScopeM A.Name
freshAbstractName fx x = do
  i <- fresh
  return $ A.Name
    { nameId          = i
    , nameConcrete    = x
    , nameBindingSite = getRange x
    , nameFixity      = fx
    }

-- | @freshAbstractName_ = freshAbstractName defaultFixity@
freshAbstractName_ :: C.Name -> ScopeM A.Name
freshAbstractName_ = freshAbstractName defaultFixity'

-- | Create a fresh abstract qualified name.
freshAbstractQName :: Fixity' -> C.Name -> ScopeM A.QName
freshAbstractQName fx x = do
  y <- freshAbstractName fx x
  m <- getCurrentModule
  return $ A.qualify m y

-- * Resolving names

data ResolvedName = VarName A.Name
                  | DefinedName Access AbstractName
                  | FieldName AbstractName           -- ^ record fields names need to be distinguished to parse copatterns
                  | ConstructorName [AbstractName]
                  | PatternSynResName AbstractName
                  | UnknownName
  deriving (Show)

-- | Look up the abstract name referred to by a given concrete name.
resolveName :: C.QName -> ScopeM ResolvedName
resolveName = resolveName' allKindsOfNames

-- | Look up the abstract name corresponding to a concrete name of
--   a certain kind.
--   Sometimes we know already that we are dealing with a constructor
--   or pattern synonym (e.g. when we have parsed a pattern).
--   Then, we can ignore conflicting definitions of that name
--   of a different kind. (See issue 822.)
resolveName' :: [KindOfName] -> C.QName -> ScopeM ResolvedName
resolveName' kinds x = do
  scope <- getScope
  let vars = AssocList.mapKeysMonotonic C.QName $ scopeLocals scope
  case lookup x vars of
    -- Case: we have a local variable x.
    Just (LocalVar y)  -> return $ VarName $ y { nameConcrete = unqualify x }
    -- Case: ... but is shadowed by some imports.
    Just (ShadowedVar y ys) -> typeError $ AmbiguousName x $ A.qualify_ y : map anameName ys
    -- Case: we do not have a local variable x.
    Nothing -> case filter ((`elem` kinds) . anameKind . fst) $ scopeLookup' x scope of
      [] -> return UnknownName
      ds | all ((==ConName) . anameKind . fst) ds ->
        return $ ConstructorName
               $ map (\ (d, _) -> updateConcreteName d $ unqualify x) ds
      [(d, a)] | anameKind d == FldName -> return $ FieldName $ updateConcreteName d (unqualify x)
      [(d, a)] | anameKind d == PatternSynName ->
                  return $ PatternSynResName (updateConcreteName d $ unqualify x)
      [(d, a)] -> return $ DefinedName a $ updateConcreteName d (unqualify x)
      ds  -> typeError $ AmbiguousName x (map (anameName . fst) ds)
  where
  updateConcreteName :: AbstractName -> C.Name -> AbstractName
  updateConcreteName d@(AbsName { anameName = an@(A.QName { qnameName = qn }) }) x =
    d { anameName = an { qnameName = qn { nameConcrete = x } } }

-- | Look up a module in the scope.
resolveModule :: C.QName -> ScopeM AbstractModule
resolveModule x = do
  ms <- scopeLookup x <$> getScope
  case ms of
    [AbsModule m why] -> return $ AbsModule (m `withRangesOfQ` x) why
    []                -> typeError $ NoSuchModule x
    ms                -> typeError $ AmbiguousModule x (map amodName ms)

-- | Get the fixity of a name. The name is assumed to be in scope.
getFixity :: C.QName -> ScopeM Fixity'
getFixity x = do
  r <- resolveName x
  case r of
    VarName y          -> return $ nameFixity y
    DefinedName _ d    -> return $ nameFixity $ qnameName $ anameName d
    FieldName d        -> return $ nameFixity $ qnameName $ anameName d
    ConstructorName ds
      | null fs        -> __IMPOSSIBLE__
      | allEqual fs    -> return $ head fs
      | otherwise      -> return defaultFixity'
      where
        fs = map (nameFixity . qnameName . anameName) ds
    PatternSynResName n -> return $ nameFixity $ qnameName $ anameName n
    UnknownName         -> __IMPOSSIBLE__

-- * Binding names

-- | Bind a variable. The abstract name is supplied as the second argument.
bindVariable :: C.Name -> A.Name -> ScopeM ()
bindVariable x y = modifyScope $ updateScopeLocals $ AssocList.insert x $ LocalVar y

-- | Bind a defined name. Must not shadow anything.
bindName :: Access -> KindOfName -> C.Name -> A.QName -> ScopeM ()
bindName acc kind x y = do
  r  <- resolveName (C.QName x)
  ys <- case r of
    FieldName d        -> typeError $ ClashingDefinition (C.QName x) $ anameName d
    DefinedName _ d    -> typeError $ ClashingDefinition (C.QName x) $ anameName d
    VarName z          -> typeError $ ClashingDefinition (C.QName x) $ A.qualify (mnameFromList []) z
    ConstructorName [] -> __IMPOSSIBLE__
    ConstructorName ds
      | kind == ConName && all ((==ConName) . anameKind) ds -> return [ AbsName y kind Defined ]
      | otherwise -> typeError $ ClashingDefinition (C.QName x) $ anameName (head' ds)
    PatternSynResName n -> typeError $ ClashingDefinition (C.QName x) $ anameName n
    UnknownName         -> return [AbsName y kind Defined]
  modifyCurrentScope $ addNamesToScope (localNameSpace acc) x ys
  where
    head' []    = {- ' -} __IMPOSSIBLE__
    head' (x:_) = x

-- | Rebind a name. Use with care!
--   Ulf, 2014-06-29: Currently used to rebind the name defined by an
--   unquoteDecl, which is a 'QuotableName' in the body, but a 'DefinedName'
--   later on.
rebindName :: Access -> KindOfName -> C.Name -> A.QName -> ScopeM ()
rebindName acc kind x y = do
  modifyCurrentScope $ removeNameFromScope (localNameSpace acc) x
  bindName acc kind x y

-- | Bind a module name.
bindModule :: Access -> C.Name -> A.ModuleName -> ScopeM ()
bindModule acc x m = modifyCurrentScope $
  addModuleToScope (localNameSpace acc) x (AbsModule m Defined)

-- | Bind a qualified module name. Adds it to the imports field of the scope.
bindQModule :: Access -> C.QName -> A.ModuleName -> ScopeM ()
bindQModule acc q m = modifyCurrentScope $ \s ->
  s { scopeImports = Map.insert q m (scopeImports s) }

-- * Module manipulation operations

-- | Clear the scope of any no names.
stripNoNames :: ScopeM ()
stripNoNames = modifyScopes $ Map.map $ mapScope_ stripN stripN
  where
    stripN = Map.filterWithKey $ const . not . isNoName

type Out = (A.Ren A.ModuleName, A.Ren A.QName)
type WSM = StateT Out ScopeM

-- | Create a new scope with the given name from an old scope. Renames
--   public names in the old scope to match the new name and returns the
--   renamings.
copyScope :: C.QName -> A.ModuleName -> Scope -> ScopeM (Scope, (A.Ren A.ModuleName, A.Ren A.QName))
copyScope oldc new s = first (inScopeBecause $ Applied oldc) <$> runStateT (copy new s) (Map.empty, Map.empty)
  where
    copy new s = do
      lift $ reportSLn "scope.copy" 20 $ "Copying scope " ++ show old ++ " to " ++ show new
      lift $ reportSLn "scope.copy" 50 $ show s
      s0 <- lift $ getNamedScope new
      s' <- mapScopeM copyD copyM s
      return $ s' { scopeName    = scopeName s0
                  , scopeParents = scopeParents s0
                  }
      where
        new' = killRange new
        old  = scopeName s

        copyM :: NameSpaceId -> ModulesInScope -> WSM ModulesInScope
        copyM ImportedNS      ms = traverse (mapM $ onMod renMod) ms
        copyM PrivateNS       _  = return Map.empty
        copyM PublicNS        ms = traverse (mapM $ onMod renMod) ms
        copyM OnlyQualifiedNS ms = traverse (mapM $ onMod renMod) ms

        copyD :: NameSpaceId -> NamesInScope -> WSM NamesInScope
        copyD ImportedNS      ds = traverse (mapM $ onName renName) ds
        copyD PrivateNS       _  = return Map.empty
        copyD PublicNS        ds = traverse (mapM $ onName renName) ds
        copyD OnlyQualifiedNS ds = traverse (mapM $ onName renName) ds

        onMod f m = do
          x <- f $ amodName m
          return m { amodName = x }

        onName f d =
          case anameKind d of
            PatternSynName -> return d  -- Pattern synonyms are simply aliased, not renamed
            _ -> do
              x <- f $ anameName d
              return d { anameName = x }

        addName x y = addNames (Map.singleton x y)
        addMod  x y = addMods (Map.singleton x y)

        addNames rd' = modify $ \(rm, rd) -> (rm, Map.union rd rd')
        addMods  rm' = modify $ \(rm, rd) -> (Map.union rm rm', rd)

        findName x = Map.lookup x <$> gets snd
        findMod  x = Map.lookup x <$> gets fst

        -- Change a binding M.x -> old.M'.y to M.x -> new.M'.y
        renName :: A.QName -> WSM A.QName
        renName x = do
          lift $ reportSLn "scope.copy" 50 $ "  Copying " ++ show x
          -- Check if we've seen it already
          my <- findName x
          case my of
            Just y -> return y
            Nothing -> do
              -- First time, generate a fresh name for it
              i <- lift fresh
              let y = qualifyQ new' . dequalify
                    $ x { qnameName = (qnameName x) { nameId = i } }
              addName x y
              return y
          where
            dequalify q = A.qnameFromList [last $ A.qnameToList q]

        -- Change a binding M.x -> old.M'.y to M.x -> new.M'.y
        renMod :: A.ModuleName -> WSM A.ModuleName
        renMod x = do
          -- Check if we've seen it already
          my <- findMod x
          case my of
            Just y -> return y
            Nothing -> do
              -- Create the name of the new module
              let y = qualifyM new' $ dequalify x
              addMod x y

              -- We need to copy the contents of included modules recursively
              s0 <- lift $ createModule False y >> getNamedScope x
              s  <- withCurrentModule' y $ copy y s0
              lift $ modifyNamedScope y (const s)
              return y
          where
            dequalify = A.mnameFromList . drop (size old) . A.mnameToList

-- | Apply an import directive and check that all the names mentioned actually
--   exist.
applyImportDirectiveM :: C.QName -> ImportDirective -> Scope -> ScopeM Scope
applyImportDirectiveM m dir scope = do
    let xs = filter doesntExist names
    reportSLn "scope.import.apply" 20 $ "non existing names: " ++ show xs
    unless (null xs)  $ typeError $ ModuleDoesntExport m xs

    let dup = targetNames \\ nub targetNames
    unless (null dup) $ typeError $ DuplicateImports m dup
    return $ applyImportDirective dir scope

  where
    names :: [ImportedName]
    names = map renFrom (renaming dir) ++ case usingOrHiding dir of
      Using  xs -> xs
      Hiding xs -> xs

    targetNames :: [ImportedName]
    targetNames = map renName (renaming dir) ++ case usingOrHiding dir of
      Using xs -> xs
      Hiding{} -> []
      where
        renName r = (renFrom r) { importedName = renTo r }

    doesntExist (ImportedName   x) = isNothing $
      Map.lookup x (allNamesInScope scope :: ThingsInScope AbstractName)
    doesntExist (ImportedModule x) = isNothing $
      Map.lookup x (allNamesInScope scope :: ThingsInScope AbstractModule)

-- | Open a module.
openModule_ :: C.QName -> ImportDirective -> ScopeM ()
openModule_ cm dir = do
  current <- getCurrentModule
  m <- amodName <$> resolveModule cm
  let acc = namespace current m
  -- Get the scope exported by module to be opened.
  s <- setScopeAccess acc <$>
        (applyImportDirectiveM cm dir . inScopeBecause (Opened cm) . removeOnlyQualified . restrictPrivate =<< getNamedScope m)
  let ns = scopeNameSpace acc s
  checkForClashes ns
  modifyCurrentScope (`mergeScope` s)
  verboseS "scope.locals" 10 $ do
    locals <- mapMaybe (\ (c,x) -> c <$ notShadowedLocal x) <$> getLocalVars
    let newdefs = Map.keys $ nsNames ns
        shadowed = List.intersect locals newdefs
    reportSLn "scope.locals" 10 $ "opening module shadows the following locals vars: " ++ show shadowed
  -- Andreas, 2014-09-03, issue 1266: shadow local variables by imported defs.
  modifyLocalVars $ AssocList.mapWithKey $ \ c x ->
    case Map.lookup c $ nsNames ns of
      Nothing -> x
      Just ys -> shadowLocal ys x
  where
    namespace m0 m1
      | not (publicOpen dir)  = PrivateNS
      | m1 `isSubModuleOf` m0 = PublicNS
      | otherwise             = ImportedNS

    -- Only checks for clashes that would lead to the same
    -- name being exported twice from the module.
    checkForClashes new = when (publicOpen dir) $ do

        old <- allThingsInScope . restrictPrivate <$> (getNamedScope =<< getCurrentModule)

        let defClashes = Map.toList $ Map.intersectionWith (,) (nsNames new) (nsNames old)
            modClashes = Map.toList $ Map.intersectionWith (,) (nsModules new) (nsModules old)

            -- No ambiguity if concrete identifier is mapped to
            -- single, identical abstract identifiers.
            realClash (_, ([x],[y])) = x /= y
            realClash _              = True

            -- No ambiguity if concrete identifier is only mapped to
            -- constructor names.
            defClash (_, (qs0, qs1)) =
              any ((/= ConName) . anameKind) (qs0 ++ qs1)

        -- We report the first clashing exported identifier.
        unlessNull (filter (\ x -> realClash x && defClash x) defClashes) $
          \ ((x, (_, q:_)) : _) -> typeError $ ClashingDefinition (C.QName x) (anameName q)

        unlessNull (filter realClash modClashes) $ \ ((_, (m0:_, m1:_)) : _) ->
          typeError $ ClashingModule (amodName m0) (amodName m1)
