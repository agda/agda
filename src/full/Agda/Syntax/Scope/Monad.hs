{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE FlexibleContexts #-}
#endif

{-| The scope monad with operations.
-}

module Agda.Syntax.Scope.Monad where

import Prelude hiding (mapM)
import Control.Arrow (first, second)
import Control.Applicative
import Control.Monad hiding (mapM)
import Control.Monad.Writer hiding (mapM)
import Control.Monad.State hiding (mapM)

import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
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
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Null (unlessNull)
import Agda.Utils.Pretty
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
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
  reportSLn "scope.createModule" 10 $ "createModule " ++ prettyShow m
  s <- getCurrentScope
  let parents = scopeName s : scopeParents s
      sm = emptyScope { scopeName           = m
                      , scopeParents        = parents
                      , scopeDatatypeModule = b }
  -- Andreas, 2015-07-02: internall error if module is not new.
  modifyScopes $ Map.insertWith __IMPOSSIBLE__ m sm

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

-- | @freshAbstractName_ = freshAbstractName noFixity'@
freshAbstractName_ :: C.Name -> ScopeM A.Name
freshAbstractName_ = freshAbstractName noFixity'

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
  deriving (Show, Eq)

-- | Look up the abstract name referred to by a given concrete name.
resolveName :: C.QName -> ScopeM ResolvedName
resolveName = resolveName' allKindsOfNames Nothing

-- | Look up the abstract name corresponding to a concrete name of
--   a certain kind and/or from a given set of names.
--   Sometimes we know already that we are dealing with a constructor
--   or pattern synonym (e.g. when we have parsed a pattern).
--   Then, we can ignore conflicting definitions of that name
--   of a different kind. (See issue 822.)
resolveName' ::
  [KindOfName] -> Maybe (Set A.Name) -> C.QName -> ScopeM ResolvedName
resolveName' kinds names x = do
  scope <- getScope
  let vars     = AssocList.mapKeysMonotonic C.QName $ scopeLocals scope
      retVar y = return $ VarName $ y { nameConcrete = unqualify x }
      aName    = A.qnameName . anameName
  case lookup x vars of
    -- Case: we have a local variable x.
    Just (LocalVar y)  -> retVar y
    -- Case: ... but is (perhaps) shadowed by some imports.
    Just (ShadowedVar y ys) -> case names of
      Nothing -> shadowed ys
      Just ns -> case filter (\y -> aName y `Set.member` ns) ys of
        [] -> retVar y
        ys -> shadowed ys
      where
      shadowed ys =
        typeError $ AmbiguousName x $ A.qualify_ y : map anameName ys
    -- Case: we do not have a local variable x.
    Nothing -> do
      -- Consider only names of one of the given kinds
      let filtKind = filter $ \ y -> anameKind (fst y) `elem` kinds
      -- Consider only names in the given set of names
          filtName = filter $ \ y -> maybe True (Set.member (aName (fst y))) names
      case filtKind $ filtName $ scopeLookup' x scope of
        [] -> return UnknownName

        ds       | all ((==ConName) . anameKind . fst) ds ->
          return $ ConstructorName $ map (upd . fst) ds

        [(d, a)] | anameKind d == FldName ->
          return $ FieldName $ upd d

        [(d, a)] | anameKind d == PatternSynName ->
          return $ PatternSynResName $ upd d

        [(d, a)] ->
          return $ DefinedName a $ upd d

        ds -> typeError $ AmbiguousName x (map (anameName . fst) ds)
  where
  upd d = updateConcreteName d $ unqualify x
  updateConcreteName :: AbstractName -> C.Name -> AbstractName
  updateConcreteName d@(AbsName { anameName = A.QName qm qn }) x =
    d { anameName = A.QName (setRange (getRange x) qm) (qn { nameConcrete = x }) }

-- | Look up a module in the scope.
resolveModule :: C.QName -> ScopeM AbstractModule
resolveModule x = do
  ms <- scopeLookup x <$> getScope
  case ms of
    [AbsModule m why] -> return $ AbsModule (m `withRangesOfQ` x) why
    []                -> typeError $ NoSuchModule x
    ms                -> typeError $ AmbiguousModule x (map amodName ms)

-- | Get the notation of a name. The name is assumed to be in scope.
getNotation
  :: C.QName
  -> Set A.Name
     -- ^ The name must correspond to one of the names in this set.
  -> ScopeM NewNotation
getNotation x ns = do
  r <- resolveName' allKindsOfNames (Just ns) x
  case r of
    VarName y           -> return $ namesToNotation x y
    DefinedName _ d     -> return $ notation d
    FieldName d         -> return $ notation d
    ConstructorName ds  -> case mergeNotations $ map notation ds of
                             [n] -> return n
                             _   -> __IMPOSSIBLE__
    PatternSynResName n -> return $ notation n
    UnknownName         -> __IMPOSSIBLE__
  where
    notation = namesToNotation x . qnameName . anameName

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
      | otherwise -> typeError $ ClashingDefinition (C.QName x) $ anameName (headWithDefault __IMPOSSIBLE__ ds)
    PatternSynResName n -> typeError $ ClashingDefinition (C.QName x) $ anameName n
    UnknownName         -> return [AbsName y kind Defined]
  modifyCurrentScope $ addNamesToScope (localNameSpace acc) x ys

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
--
--   Data and record types share a common abstract name with their module.
--   This invariant needs to be preserved by @copyScope@, since constructors
--   (fields) can be qualified by their data (record) type name (as an
--   alternative to qualification by their module).
--   (See Issue 836).
copyScope :: C.QName -> A.ModuleName -> Scope -> ScopeM (Scope, (A.Ren A.ModuleName, A.Ren A.QName))
copyScope oldc new s = first (inScopeBecause $ Applied oldc) <$> runStateT (copy new s) ([], [])
  where
    -- | A memoizing algorithm, the renamings serving as memo structure.
    copy :: A.ModuleName -> Scope -> StateT (A.Ren A.ModuleName, A.Ren A.QName) ScopeM Scope
    copy new s = do
      lift $ reportSLn "scope.copy" 20 $ "Copying scope " ++ show old ++ " to " ++ show new
      lift $ reportSLn "scope.copy" 50 $ show s
      s0 <- lift $ getNamedScope new
      -- Delete private names, then copy names and modules.
      s' <- mapScopeM_ copyD copyM $ setNameSpace PrivateNS emptyNameSpace s
      -- Fix name and parent.
      return $ s' { scopeName    = scopeName s0
                  , scopeParents = scopeParents s0
                  }
      where
        rnew = getRange new
        new' = killRange new
        newL = A.mnameToList new'
        old  = scopeName s

        copyD :: NamesInScope -> WSM NamesInScope
        copyD = traverse $ mapM $ onName renName

        copyM :: ModulesInScope -> WSM ModulesInScope
        copyM = traverse $ mapM $ lensAmodName renMod

        onName :: (A.QName -> WSM A.QName) -> AbstractName -> WSM AbstractName
        onName f d =
          case anameKind d of
            PatternSynName -> return d  -- Pattern synonyms are simply aliased, not renamed
            _ -> lensAnameName f d

        -- Adding to memo structure.
        addName x y = modify $ second $ ((x, y):)
        addMod  x y = modify $ first  $ ((x, y):)

        -- Querying the memo structure.
        findName x = lookup x <$> gets snd
        findMod  x = lookup x <$> gets fst

        -- Change a binding M.x -> old.M'.y to M.x -> new.M'.y
        renName :: A.QName -> WSM A.QName
        renName x = do
          -- Check whether we have already seen a module of the same name.
          -- If yes, use its copy as @y@.
          y <- ifJustM (findMod $ qnameToMName x) (return . mnameToQName) $ {- else -} do
            -- First time, generate a fresh name for it.
            i <- lift fresh
            return $ A.qualify new' $ (qnameName x) { nameId = i }
          lift $ reportSLn "scope.copy" 50 $ "  Copying " ++ show x ++ " to " ++ show y
          -- Andreas, 2015-08-11 Issue 1619:
          -- Names copied by a module macro should get the module macro's
          -- range as declaration range
          -- (maybe rather the one of the open statement).
          -- For now, we just set their range
          -- to the new module name's one, which fixes issue 1619.
          y <- return $ setRange rnew y
          addName x y
          return y

        -- Change a binding M.x -> old.M'.y to M.x -> new.M'.y
        renMod :: A.ModuleName -> WSM A.ModuleName
        renMod x = do
          -- Andreas, issue 1607:
          -- If we have already copied this module, return the copy.
          ifJustM (findMod x) return $ {- else -} do

          -- Check whether we have seen it already, yet as  name.
          -- If yes, use its copy as @y@.
          y <- ifJustM (findName $ mnameToQName x) (return . qnameToMName) $ {- else -} do
             -- Andreas, Jesper, 2015-07-02: Issue 1597
             -- Don't blindly drop a prefix of length of the old qualifier.
             -- If things are imported by open public they do not have the old qualifier
             -- as prefix.  Those need just to be linked, not copied.
             -- return $ A.mnameFromList $ (newL ++) $ drop (size old) $ A.mnameToList x
             caseMaybe (maybePrefixMatch (A.mnameToList old) (A.mnameToList x)) (return x) $ \ suffix -> do
               return $ A.mnameFromList $ newL ++ suffix
          -- Andreas, Jesper, 2015-07-02: Issue 1597
          -- Don't copy a module over itself, it will just be emptied of its contents.
          if (x == y) then return x else do
          addMod x y
          -- We need to copy the contents of included modules recursively
          lift $ createModule False y
          s0 <- lift $ getNamedScope x
          s  <- withCurrentModule' y $ copy y s0
          lift $ modifyNamedScope y (const s)
          return y

-- | Apply an import directive and check that all the names mentioned actually
--   exist.
applyImportDirectiveM :: C.QName -> ImportDirective -> Scope -> ScopeM Scope
applyImportDirectiveM m dir scope = do
    let xs = filter doesntExist names
    reportSLn "scope.import.apply" 20 $ "non existing names: " ++ show xs
    unless (null xs)  $ typeError $ ModuleDoesntExport m xs

    let extraModules =
          [ x | ImportedName x <- names,
                let mx = ImportedModule x,
                 not $ doesntExist mx,
                 notElem mx names ]
        dir' = addExtraModules extraModules dir

    dir' <- sanityCheck dir'

    let dup = targetNames \\ nub targetNames
    unless (null dup) $ typeError $ DuplicateImports m dup
    return $ applyImportDirective dir' scope

  where
    names :: [ImportedName]
    names = map renFrom (renaming dir) ++ hiding dir ++ case using dir of
      Using  xs     -> xs
      UseEverything -> []

    targetNames :: [ImportedName]
    targetNames = map renName (renaming dir) ++ case using dir of
      Using xs      -> xs
      UseEverything -> []
      where
        renName r = (renFrom r) { importedName = renTo r }

    sanityCheck dir =
      case (using dir, hiding dir) of
        (Using xs, ys) -> do
          let uselessHiding = [ x | x@ImportedName{} <- ys ] ++
                              [ x | x@(ImportedModule y) <- ys, ImportedName y `notElem` names ]
          unless (null uselessHiding) $ typeError $ GenericError $ "Hiding " ++ intercalate ", " (map show uselessHiding)
                                                                ++ " has no effect"
          return dir{ hiding = [] }
        _ -> return dir

    addExtraModules :: [C.Name] -> ImportDirective -> ImportDirective
    addExtraModules extra dir =
      dir{ using =
              case using dir of
                Using xs      -> Using $ concatMap addExtra xs
                UseEverything -> UseEverything
         , hiding   = concatMap addExtra      (hiding dir)
         , renaming = concatMap extraRenaming (renaming dir)
         }
      where
        addExtra f@(ImportedName y) | elem y extra = [f, ImportedModule y]
        addExtra m = [m]

        extraRenaming r =
          case renFrom r of
            ImportedName y | elem y extra -> [r, r{ renFrom = ImportedModule y }]
            _ -> [r]

    doesntExist (ImportedName   x) = isNothing $
      Map.lookup x (allNamesInScope scope :: ThingsInScope AbstractName)
    doesntExist (ImportedModule x) = isNothing $
      Map.lookup x (allNamesInScope scope :: ThingsInScope AbstractModule)

-- | Open a module.
openModule_ :: C.QName -> ImportDirective -> ScopeM ()
openModule_ cm dir = do
  current <- getCurrentModule
  m <- amodName <$> resolveModule cm
  let acc | not (publicOpen dir)      = PrivateNS
          | m `isSubModuleOf` current = PublicNS
          | otherwise                 = ImportedNS
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
