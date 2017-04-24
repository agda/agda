{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}

{-| The scope monad with operations.
-}

module Agda.Syntax.Scope.Monad where

import Prelude hiding (mapM)
import Control.Arrow (first, second, (***))
import Control.Applicative
import Control.Monad hiding (mapM, forM)
import Control.Monad.Writer hiding (mapM, forM)
import Control.Monad.State hiding (mapM, forM)

import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable hiding (for)

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract (ScopeCopyInfo(..), initCopyInfo)
import Agda.Syntax.Concrete as C
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Options

import qualified Agda.Utils.AssocList as AssocList
import Agda.Utils.Function
import Agda.Utils.Functor
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
setCurrentModule m = modifyScope $ \s -> s { scopeCurrent = m }

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
  -- Andreas, 2015-07-02: internal error if module is not new.
  -- Ulf, 2016-02-15: It's not new if multiple imports (#1770).
  modifyScopes $ Map.insertWith const m sm

-- | Apply a function to the scope map.
modifyScopes :: (Map A.ModuleName Scope -> Map A.ModuleName Scope) -> ScopeM ()
modifyScopes f = modifyScope $ \s -> s { scopeModules = f $ scopeModules s }

-- | Apply a function to the given scope.
modifyNamedScope :: A.ModuleName -> (Scope -> Scope) -> ScopeM ()
modifyNamedScope m f = modifyScopes $ Map.adjust f m

setNamedScope :: A.ModuleName -> Scope -> ScopeM ()
setNamedScope m s = modifyNamedScope m $ const s

-- | Apply a monadic function to the top scope.
modifyNamedScopeM :: A.ModuleName -> (Scope -> ScopeM (a, Scope)) -> ScopeM a
modifyNamedScopeM m f = do
  (a, s) <- f =<< getNamedScope m
  setNamedScope m s
  return a

-- | Apply a function to the current scope.
modifyCurrentScope :: (Scope -> Scope) -> ScopeM ()
modifyCurrentScope f = getCurrentModule >>= (`modifyNamedScope` f)

modifyCurrentScopeM :: (Scope -> ScopeM (a, Scope)) -> ScopeM a
modifyCurrentScopeM f = getCurrentModule >>= (`modifyNamedScopeM` f)

-- | Apply a function to the public or private name space.
modifyCurrentNameSpace :: NameSpaceId -> (NameSpace -> NameSpace) -> ScopeM ()
modifyCurrentNameSpace acc f = modifyCurrentScope $ updateScopeNameSpaces $
  AssocList.updateAt acc f

setContextPrecedence :: Precedence -> ScopeM ()
setContextPrecedence p = modifyScope_ $ \s -> s { scopePrecedence = p }

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
modifyLocalVars = modifyScope_ . updateScopeLocals

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

data ResolvedName
  =   -- | Local variable bound by λ, Π, module telescope, pattern, @let@.
    VarName
    { resolvedVar      :: A.Name
    , resolvedLetBound :: Bool    -- ^ Variable bound by @let@?
    }

  |   -- | Function, data/record type, postulate.
    DefinedName Access AbstractName

  |   -- | Record field name.  Needs to be distinguished to parse copatterns.
    FieldName [AbstractName]

  |   -- | Data or record constructor name.
    ConstructorName [AbstractName]

  |   -- | Name of pattern synonym.
    PatternSynResName AbstractName

  |   -- | Unbound name.
    UnknownName
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
      retVar y = return . VarName y{ nameConcrete = unqualify x }
      aName    = A.qnameName . anameName
  case lookup x vars of
    -- Case: we have a local variable x.
    Just (LocalVar y b []) -> retVar y b
    -- Case: ... but is (perhaps) shadowed by some imports.
    Just (LocalVar y b ys) -> case names of
      Nothing -> shadowed ys
      Just ns -> case filter (\ y -> aName y `Set.member` ns) ys of
        [] -> retVar y b
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

        ds       | all ((==FldName) . anameKind . fst) ds ->
          return $ FieldName $ map (upd . fst) ds

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
    VarName y _         -> return $ namesToNotation x y
    DefinedName _ d     -> return $ notation d
    FieldName ds        -> return $ oneNotation ds
    ConstructorName ds  -> return $ oneNotation ds
    PatternSynResName n -> return $ notation n
    UnknownName         -> __IMPOSSIBLE__
  where
    notation = namesToNotation x . qnameName . anameName
    oneNotation ds =
      case mergeNotations $ map notation ds of
        [n] -> n
        _   -> __IMPOSSIBLE__

-- * Binding names

-- | Bind a variable.
bindVariable
  :: Bool    -- ^ Let-bound variable?
  -> C.Name  -- ^ Concrete name.
  -> A.Name  -- ^ Abstract name.
  -> ScopeM ()
bindVariable b x y = modifyScope_ $ updateScopeLocals $ AssocList.insert x $ LocalVar y b []

-- | Bind a defined name. Must not shadow anything.
bindName :: Access -> KindOfName -> C.Name -> A.QName -> ScopeM ()
bindName acc kind x y = do
  r  <- resolveName (C.QName x)
  ys <- case r of
    -- Binding an anonymous declaration always succeeds.
    -- In case it's not the first one, we simply remove the one that came before
    UnknownName   | isNoName x -> success
    DefinedName{} | isNoName x -> success <* modifyCurrentScope (removeNameFromScope PrivateNS x)
    DefinedName _ d     -> clash $ anameName d
    VarName z _         -> clash $ A.qualify (mnameFromList []) z
    FieldName       ds  -> ambiguous FldName ds
    ConstructorName ds  -> ambiguous ConName ds
    PatternSynResName n -> clash $ anameName n
    UnknownName         -> success
  let ns = if isNoName x then PrivateNS else localNameSpace acc
  modifyCurrentScope $ addNamesToScope ns x ys
  where
    success = return [ AbsName y kind Defined ]
    clash   = typeError . ClashingDefinition (C.QName x)

    ambiguous k ds@(d:_) =
      if kind == k && all ((==k) . anameKind) ds
      then success else clash $ anameName d
    ambiguous k [] = __IMPOSSIBLE__

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
stripNoNames = modifyScopes $ Map.map $ mapScope_ stripN stripN id
  where
    stripN = Map.filterWithKey $ const . not . isNoName

type WSM = StateT ScopeMemo ScopeM

data ScopeMemo = ScopeMemo
  { memoNames   :: A.Ren A.QName
  , memoModules :: [(ModuleName, (ModuleName, Bool))]
    -- ^ Bool: did we copy recursively? We need to track this because we don't
    --   copy recursively when creating new modules for reexported functions
    --   (issue1985), but we might need to copy recursively later.
  }

memoToScopeInfo :: ScopeMemo -> ScopeCopyInfo
memoToScopeInfo (ScopeMemo names mods) =
  ScopeCopyInfo { renNames   = names
                , renModules = [ (x, y) | (x, (y, _)) <- mods ] }

-- | Create a new scope with the given name from an old scope. Renames
--   public names in the old scope to match the new name and returns the
--   renamings.
copyScope :: C.QName -> A.ModuleName -> Scope -> ScopeM (Scope, ScopeCopyInfo)
copyScope oldc new0 s = (inScopeBecause (Applied oldc) *** memoToScopeInfo) <$> runStateT (copy new0 s) (ScopeMemo [] [])
  where
    copy :: A.ModuleName -> Scope -> WSM Scope
    copy new s = do
      lift $ reportSLn "scope.copy" 20 $ "Copying scope " ++ show old ++ " to " ++ show new
      lift $ reportSLn "scope.copy" 50 $ show s
      s0 <- lift $ getNamedScope new
      -- Delete private names, then copy names and modules. Recompute inScope
      -- set rather than trying to copy it.
      s' <- recomputeInScopeSets <$> mapScopeM_ copyD copyM return (setNameSpace PrivateNS emptyNameSpace s)
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
        addName x y     = modify $ \ i -> i { memoNames   = (x, y)        : memoNames   i }
        addMod  x y rec = modify $ \ i -> i { memoModules = (x, (y, rec)) : filter ((/= x) . fst) (memoModules i) }

        -- Querying the memo structure.
        findName x = lookup x <$> gets memoNames
        findMod  x = lookup x <$> gets memoModules

        refresh :: A.Name -> WSM A.Name
        refresh x = do
          i <- lift fresh
          return $ x { nameId = i }

        -- Change a binding M.x -> old.M'.y to M.x -> new.M'.y
        renName :: A.QName -> WSM A.QName
        renName x = do
          -- Issue 1985: For re-exported names we can't use new' as the
          -- module, since it has the wrong telescope. Example:
          --
          --    module M1 (A : Set) where
          --      module M2 (B : Set) where
          --        postulate X : Set
          --      module M3 (C : Set) where
          --        module M4 (D E : Set) where
          --          open M2 public
          --
          --    module M = M1.M3 A C
          --
          -- Here we can't copy M1.M2.X to M.M4.X since we need
          -- X : (B : Set) → Set, but M.M4 has telescope (D E : Set). Thus, we
          -- would break the invariant that all functions in a module share the
          -- module telescope. Instead we copy M1.M2.X to M.M2.X for a fresh
          -- module M2 that gets the right telescope.
          m <- case x `isInModule` old of
                 True  -> return new'
                 False -> renMod' False (qnameModule x)
                          -- Don't copy recursively here, we only know that the
                          -- current name x should be copied.
          -- Generate a fresh name for the target.
          -- Andreas, 2015-08-11 Issue 1619:
          -- Names copied by a module macro should get the module macro's
          -- range as declaration range
          -- (maybe rather the one of the open statement).
          -- For now, we just set their range
          -- to the new module name's one, which fixes issue 1619.
          y <- setRange rnew . A.qualify m <$> refresh (qnameName x)
          lift $ reportSLn "scope.copy" 50 $ "  Copying " ++ show x ++ " to " ++ show y
          addName x y
          return y

        -- Change a binding M.x -> old.M'.y to M.x -> new.M'.y
        renMod :: A.ModuleName -> WSM A.ModuleName
        renMod = renMod' True

        renMod' rec x = do
          -- Andreas, issue 1607:
          -- If we have already copied this module, return the copy.
          z <- findMod x
          case z of
            Just (y, False) | rec -> y <$ copyRec x y
            Just (y, _)           -> return y
            Nothing -> do
            -- Ulf (issue 1985): If copying a reexported module we put it at the
            -- top-level, to make sure we don't mess up the invariant that all
            -- (abstract) names M.f share the argument telescope of M.
            let newM | x `isSubModuleOf` old = newL
                     | otherwise             = mnameToList new0

            y <- do
               -- Andreas, Jesper, 2015-07-02: Issue 1597
               -- Don't blindly drop a prefix of length of the old qualifier.
               -- If things are imported by open public they do not have the old qualifier
               -- as prefix.  Those need just to be linked, not copied.
               -- return $ A.mnameFromList $ (newL ++) $ drop (size old) $ A.mnameToList x
               -- caseMaybe (stripPrefix (A.mnameToList old) (A.mnameToList x)) (return x) $ \ suffix -> do
               --   return $ A.mnameFromList $ newL ++ suffix
               -- Ulf, 2016-02-22: #1726
               -- We still need to copy modules from 'open public'. Same as in renName.
               y <- refresh (last $ A.mnameToList x)
               return $ A.mnameFromList $ newM ++ [y]
            -- Andreas, Jesper, 2015-07-02: Issue 1597
            -- Don't copy a module over itself, it will just be emptied of its contents.
            if (x == y) then return x else do
            lift $ reportSLn "scope.copy" 50 $ "  Copying module " ++ show x ++ " to " ++ show y
            addMod x y rec
            lift $ createModule False y
            -- We need to copy the contents of included modules recursively (only when 'rec')
            when rec $ copyRec x y
            return y
          where
            copyRec x y = do
              s0 <- lift $ getNamedScope x
              s  <- withCurrentModule' y $ copy y s0
              lift $ modifyNamedScope y (const s)

-- | Apply an import directive and check that all the names mentioned actually
--   exist.
applyImportDirectiveM :: C.QName -> C.ImportDirective -> Scope -> ScopeM (A.ImportDirective, Scope)
applyImportDirectiveM m dir@ImportDirective{ impRenaming = ren, using = u, hiding = h } scope = do
    -- Translate exported names to abstract syntax.
    -- Raise error if unsuccessful.
    caseMaybe mNamesA doesntExport $ \ namesA -> do

    let extraModules =
          [ x | ImportedName x <- names,
                let mx = ImportedModule x,
                 not $ doesntExist mx,
                 notElem mx names ]
        dir' = addExtraModules extraModules dir

    dir' <- sanityCheck dir'

    -- Check for duplicate imports in a single import directive.
    -- @dup@ : To be imported names that are mentioned more than once.
    let dup = targetNames \\ nub targetNames
    unless (null dup) $ typeError $ DuplicateImports m dup

    -- Apply the import directive.
    let scope' = applyImportDirective dir' scope

    -- Look up the defined names in the new scope.
    let namesInScope'   = (allNamesInScope scope' :: ThingsInScope AbstractName)
    let modulesInScope' = (allNamesInScope scope' :: ThingsInScope AbstractModule)
    let look x = head . Map.findWithDefault __IMPOSSIBLE__ x
    -- We set the ranges to the ranges of the concrete names in order to get
    -- highlighting for the names in the import directive.
    let definedA = for definedNames $ \case
          ImportedName   x -> ImportedName   . (x,) . setRange (getRange x) . anameName $ look x namesInScope'
          ImportedModule x -> ImportedModule . (x,) . setRange (getRange x) . amodName  $ look x modulesInScope'

    let adir = mapImportDir namesA definedA dir
    return (adir, scope') -- TODO Issue 1714: adir

  where
    -- | Names in the @using@ directive.
    usingNames :: [ImportedName]
    usingNames = case u of
      Using  xs     -> xs
      UseEverything -> []

    -- | All names from the imported module mentioned in the import directive.
    names :: [ImportedName]
    names = map renFrom ren ++ h ++ usingNames

    -- | Names defined by the import (targets of renaming).
    definedNames :: [ImportedName]
    definedNames = map renTo ren

    -- | Names to be in scope after import.
    targetNames :: [ImportedName]
    targetNames = definedNames ++ usingNames

    sanityCheck dir =
      case (using dir, hiding dir) of
        (Using xs, ys) -> do
          let uselessHiding = [ x | x@ImportedName{} <- ys ] ++
                              [ x | x@(ImportedModule y) <- ys, ImportedName y `notElem` names ]
          unless (null uselessHiding) $ typeError $ GenericError $ "Hiding " ++ intercalate ", " (map show uselessHiding)
                                                                ++ " has no effect"
          return dir{ hiding = [] }
        _ -> return dir

    addExtraModules :: [C.Name] -> C.ImportDirective -> C.ImportDirective
    addExtraModules extra dir =
      dir{ using =
              case using dir of
                Using xs      -> Using $ concatMap addExtra xs
                UseEverything -> UseEverything
         , hiding      = concatMap addExtra      (hiding dir)
         , impRenaming = concatMap extraRenaming (impRenaming dir)
         }
      where
        addExtra f@(ImportedName y) | elem y extra = [f, ImportedModule y]
        addExtra m = [m]

        extraRenaming r@(Renaming from to rng) =
          case (from, to) of
            (ImportedName y, ImportedName z) | elem y extra ->
              [r, Renaming (ImportedModule y) (ImportedModule z) rng]
            _ -> [r]

    -- | Names and modules (abstract) in scope before the import.
    namesInScope   = (allNamesInScope scope :: ThingsInScope AbstractName)
    modulesInScope = (allNamesInScope scope :: ThingsInScope AbstractModule)

    -- | AST versions of the concrete names from the imported module.
    --   @Nothing@ is one of the names is not exported.
    mNamesA = forM names $ \case
      ImportedName x   -> ImportedName   . (x,) . setRange (getRange x) . anameName . head <$> Map.lookup x namesInScope
      ImportedModule x -> ImportedModule . (x,) . setRange (getRange x) . amodName  . head <$> Map.lookup x modulesInScope

    head = headWithDefault __IMPOSSIBLE__

    -- For the sake of the error message, we (re)compute the list of unresolved names.
    doesntExport = do
      -- Names @xs@ mentioned in the import directive @dir@ but not in the @scope@.
      let xs = filter doesntExist names
      reportSLn "scope.import.apply" 20 $ "non existing names: " ++ show xs
      typeError $ ModuleDoesntExport m xs

    doesntExist (ImportedName   x) = isNothing $ Map.lookup x namesInScope
    doesntExist (ImportedModule x) = isNothing $ Map.lookup x modulesInScope

-- | A finite map for @ImportedName@s.
lookupImportedName
  :: (Eq a, Eq b)
  => ImportedName' a b
  -> [ImportedName' (a,c) (b,d)]
  -> ImportedName' c d
lookupImportedName (ImportedName x) = loop where
  loop [] = __IMPOSSIBLE__
  loop (ImportedName (y,z) : _) | x == y = ImportedName z
  loop (_ : ns) = loop ns
lookupImportedName (ImportedModule x) = loop where
  loop [] = __IMPOSSIBLE__
  loop (ImportedModule (y,z) : _) | x == y = ImportedModule z
  loop (_ : ns) = loop ns

-- | Translation of @ImportDirective@.
mapImportDir
  :: (Eq a, Eq b)
  => [ImportedName' (a,c) (b,d)]  -- ^ Translation of imported names.
  -> [ImportedName' (a,c) (b,d)]  -- ^ Translation of names defined by this import.
  -> ImportDirective' a b
  -> ImportDirective' c d
mapImportDir src tgt (ImportDirective r u h ren open) =
  ImportDirective r
    (mapUsing src u)
    (map (`lookupImportedName` src) h)
    (map (mapRenaming src tgt) ren) open

-- | Translation of @Using or Hiding@.
mapUsing
  :: (Eq a, Eq b)
  => [ImportedName' (a,c) (b,d)] -- ^ Translation of names in @using@ or @hiding@ list.
  -> Using' a b
  -> Using' c d
mapUsing src UseEverything = UseEverything
mapUsing src (Using  xs) = Using $ map (`lookupImportedName` src) xs

-- | Translation of @Renaming@.
mapRenaming
  ::  (Eq a, Eq b)
  => [ImportedName' (a,c) (b,d)]  -- ^ Translation of 'renFrom' names.
  -> [ImportedName' (a,c) (b,d)]  -- ^ Translation of 'rento' names.
  -> Renaming' a b
  -> Renaming' c d
mapRenaming src tgt (Renaming from to r) =
  Renaming (lookupImportedName from src) (lookupImportedName to tgt) r

-- | Open a module.
openModule_ :: C.QName -> C.ImportDirective -> ScopeM A.ImportDirective
openModule_ cm dir = do
  current <- getCurrentModule
  m <- amodName <$> resolveModule cm
  let acc | not (publicOpen dir)      = PrivateNS
          | m `isSubModuleOf` current = PublicNS
          | otherwise                 = ImportedNS

  -- Get the scope exported by module to be opened.
  (adir, s') <- applyImportDirectiveM cm dir . inScopeBecause (Opened cm) . removeOnlyQualified . restrictPrivate =<< getNamedScope m
  let s  = setScopeAccess acc s'
  let ns = scopeNameSpace acc s
  checkForClashes ns
  modifyCurrentScope (`mergeScope` s)

  -- Importing names might shadow existing locals.
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

  return adir

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
            -- constructor names or only to projection names.
            defClash (_, (qs0, qs1)) = not $ all (== ConName) ks || all (==FldName) ks
              where ks = map anameKind $ qs0 ++ qs1
        -- We report the first clashing exported identifier.
        unlessNull (filter (\ x -> realClash x && defClash x) defClashes) $
          \ ((x, (_, q:_)) : _) -> typeError $ ClashingDefinition (C.QName x) (anameName q)

        unlessNull (filter realClash modClashes) $ \ ((_, (m0:_, m1:_)) : _) ->
          typeError $ ClashingModule (amodName m0) (amodName m1)
