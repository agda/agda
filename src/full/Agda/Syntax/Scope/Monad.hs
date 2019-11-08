{-# LANGUAGE NondecreasingIndentation #-}

{-| The scope monad with operations.
-}

module Agda.Syntax.Scope.Monad where

import Prelude hiding (mapM, any, all, null)

import Control.Arrow ((***))
import Control.Monad hiding (mapM, forM)
import Control.Monad.Writer hiding (mapM, forM)
import Control.Monad.State hiding (mapM, forM)

import Data.Either ( partitionEithers )
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable (all)
import Data.Traversable hiding (for)

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract (ScopeCopyInfo(..))
import Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Fixity
import Agda.Syntax.Concrete.Definitions (DeclarationWarning(..)) -- TODO: move the relevant warnings out of there
import Agda.Syntax.Scope.Base as A

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Positivity.Occurrence (Occurrence)
import Agda.TypeChecking.Warnings ( warning )

import qualified Agda.Utils.AssocList as AssocList
import Agda.Utils.Except
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.NonemptyList as NonemptyList
import Agda.Utils.Pretty

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * The scope checking monad
---------------------------------------------------------------------------

-- | To simplify interaction between scope checking and type checking (in
--   particular when chasing imports), we use the same monad.
type ScopeM = TCM

-- Debugging

printLocals :: Int -> String -> ScopeM ()
printLocals v s = verboseS "scope.top" v $ do
  locals <- getLocalVars
  reportSLn "scope.top" v $ s ++ " " ++ prettyShow locals

---------------------------------------------------------------------------
-- * General operations
---------------------------------------------------------------------------

isDatatypeModule :: ReadTCState m => A.ModuleName -> m (Maybe DataOrRecord)
isDatatypeModule m = do
   scopeDatatypeModule . Map.findWithDefault __IMPOSSIBLE__ m <$> useScope scopeModules

getCurrentModule :: ReadTCState m => m A.ModuleName
getCurrentModule = setRange noRange <$> useScope scopeCurrent

setCurrentModule :: MonadTCState m => A.ModuleName -> m ()
setCurrentModule m = modifyScope $ set scopeCurrent m

withCurrentModule :: (ReadTCState m, MonadTCState m) => A.ModuleName -> m a -> m a
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
  case Map.lookup m (scope ^. scopeModules) of
    Just s  -> return s
    Nothing -> do
      reportSLn "" 0 $ "ERROR: In scope\n" ++ prettyShow scope ++ "\nNO SUCH SCOPE " ++ prettyShow m
      __IMPOSSIBLE__

getCurrentScope :: ScopeM Scope
getCurrentScope = getNamedScope =<< getCurrentModule

-- | Create a new module with an empty scope.
--   (@Just@ if it is a datatype or record module.)
createModule :: Maybe DataOrRecord -> A.ModuleName -> ScopeM ()
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
modifyScopes = modifyScope . over scopeModules

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

setContextPrecedence :: PrecedenceStack -> ScopeM ()
setContextPrecedence = modifyScope_ . set scopePrecedence

withContextPrecedence :: ReadTCState m => Precedence -> m a -> m a
withContextPrecedence p =
  locallyTCState (stScope . scopePrecedence) $ pushPrecedence p

getLocalVars :: ReadTCState m => m LocalVars
getLocalVars = useScope scopeLocals

modifyLocalVars :: (LocalVars -> LocalVars) -> ScopeM ()
modifyLocalVars = modifyScope_ . updateScopeLocals

setLocalVars :: LocalVars -> ScopeM ()
setLocalVars vars = modifyLocalVars $ const vars

-- | Run a computation without changing the local variables.
withLocalVars :: ScopeM a -> ScopeM a
withLocalVars = bracket_ getLocalVars setLocalVars

-- | Check that the newly added variable have unique names.

withCheckNoShadowing :: ScopeM a -> ScopeM a
withCheckNoShadowing = bracket_ getLocalVars $ \ lvarsOld ->
  checkNoShadowing lvarsOld =<< getLocalVars

checkNoShadowing :: LocalVars  -- ^ Old local scope
                 -> LocalVars  -- ^ New local scope
                 -> ScopeM ()
checkNoShadowing old new = do
  -- LocalVars is currnently an AssocList so the difference between
  -- two local scope is the left part of the new one.
  let diff = dropEnd (length old) new
  -- Filter out the underscores.
  let newNames = filter (not . isNoName) $ AssocList.keys diff
  -- Associate each name to its occurrences.
  let nameOccs = Map.toList $ Map.fromListWith (++) $ map pairWithRange newNames
  -- Warn if we have two or more occurrences of the same name.
  unlessNull (filter (atLeastTwo . snd) nameOccs) $ \ conflicts -> do
    warning $ NicifierIssue $ ShadowingInTelescope conflicts
  where
    pairWithRange :: C.Name -> (C.Name, [Range])
    pairWithRange n = (n, [getRange n])

    atLeastTwo :: [a] -> Bool
    atLeastTwo (_ : _ : _) = True
    atLeastTwo _ = False

getVarsToBind :: ScopeM LocalVars
getVarsToBind = useScope scopeVarsToBind

addVarToBind :: C.Name -> LocalVar -> ScopeM ()
addVarToBind x y = modifyScope_ $ updateVarsToBind $ AssocList.insert x y

-- | After collecting some variable names in the scopeVarsToBind,
--   bind them all simultaneously.
bindVarsToBind :: ScopeM ()
bindVarsToBind = do
  vars <- getVarsToBind
  modifyLocalVars (vars++)
  printLocals 10 "bound variables:"
  modifyScope_ $ setVarsToBind []

---------------------------------------------------------------------------
-- * Names
---------------------------------------------------------------------------

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
    , nameIsRecordName = False
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

freshAbstractQName' :: C.Name -> ScopeM A.QName
freshAbstractQName' x = do
  fx <- getConcreteFixity x
  freshAbstractQName fx x

-- | Create a concrete name that is not yet in scope.
freshConcreteName :: Range -> Int -> String -> ScopeM C.Name
freshConcreteName r i s = do
  let cname = C.Name r C.NotInScope [Id $ stringToRawName $ s ++ show i]
  rn <- resolveName $ C.QName cname
  case rn of
    UnknownName -> return cname
    _           -> freshConcreteName r (i+1) s

---------------------------------------------------------------------------
-- * Resolving names
---------------------------------------------------------------------------

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
  KindsOfNames -> Maybe (Set A.Name) -> C.QName -> ScopeM ResolvedName
resolveName' kinds names x = runExceptT (tryResolveName kinds names x) >>= \case
  Left ys  -> traceCall (SetRange $ getRange x) $ typeError $ AmbiguousName x ys
  Right x' -> return x'

tryResolveName
  :: (ReadTCState m, MonadError (NonemptyList A.QName) m)
  => KindsOfNames       -- ^ Restrict search to these kinds of names.
  -> Maybe (Set A.Name) -- ^ Unless 'Nothing', restrict search to match any of these names.
  -> C.QName            -- ^ Name to be resolved
  -> m ResolvedName     -- ^ If illegally ambiguous, throw error with the ambiguous name.
tryResolveName kinds names x = do
  scope <- getScope
  let vars     = AssocList.mapKeysMonotonic C.QName $ scope ^. scopeLocals
  case lookup x vars of
    -- Case: we have a local variable x, but is (perhaps) shadowed by some imports ys.
    Just (LocalVar y b ys) ->
      -- We may ignore the imports filtered out by the @names@ filter.
      ifNull (filterNames id ys)
        {-then-} (return $ VarName y{ nameConcrete = unqualify x } b)
        {-else-} $ \ ys' ->
          throwError $ A.qualify_ y :! map anameName ys'
    -- Case: we do not have a local variable x.
    Nothing -> do
      -- Consider only names of one of the given kinds
      let filtKind = filter $ (`elemKindsOfNames` kinds) . anameKind . fst
      -- Consider only names in the given set of names
      caseListNe (filtKind $ filterNames fst $ scopeLookup' x scope) (return UnknownName) $ \ case
        ds       | all ((ConName ==) . anameKind . fst) ds ->
          return $ ConstructorName $ fmap (upd . fst) ds

        ds       | all ((FldName ==) . anameKind . fst) ds ->
          return $ FieldName $ fmap (upd . fst) ds

        ds       | all ((PatternSynName ==) . anameKind . fst) ds ->
          return $ PatternSynResName $ fmap (upd . fst) ds

        (d, a) :! [] ->
          return $ DefinedName a $ upd d

        ds -> throwError $ fmap (anameName . fst) ds
  where
  -- @names@ intended semantics: a filter on names.
  -- @Nothing@: don't filter out anything.
  -- @Just ns@: filter by membership in @ns@.
  filterNames :: forall a. (a -> AbstractName) -> [a] -> [a]
  filterNames = case names of
    Nothing -> \ f -> id
    Just ns -> \ f -> filter $ (`Set.member` ns) . A.qnameName . anameName . f
    -- lambda-dropped style by intention
  upd d = updateConcreteName d $ unqualify x
  updateConcreteName :: AbstractName -> C.Name -> AbstractName
  updateConcreteName d@(AbsName { anameName = A.QName qm qn }) x =
    d { anameName = A.QName (setRange (getRange x) qm) (qn { nameConcrete = x }) }

-- | Look up a module in the scope.
resolveModule :: C.QName -> ScopeM AbstractModule
resolveModule x = do
  ms <- scopeLookup x <$> getScope
  caseListNe ms (typeError $ NoSuchModule x) $ \ case
    AbsModule m why :! [] -> return $ AbsModule (m `withRangeOf` x) why
    ms                    -> typeError $ AmbiguousModule x (fmap amodName ms)

-- | Get the fixity of a not yet bound name.
getConcreteFixity :: C.Name -> ScopeM Fixity'
getConcreteFixity x = Map.findWithDefault noFixity' x <$> useScope scopeFixities

-- | Get the polarities of a not yet bound name.
getConcretePolarity :: C.Name -> ScopeM (Maybe [Occurrence])
getConcretePolarity x = Map.lookup x <$> useScope scopePolarities

instance MonadFixityError ScopeM where
  throwMultipleFixityDecls xs         = case xs of
    (x, _) : _ -> setCurrentRange (getRange x) $ typeError $ MultipleFixityDecls xs
    []         -> __IMPOSSIBLE__
  throwMultiplePolarityPragmas xs     = case xs of
    x : _ -> setCurrentRange (getRange x) $ typeError $ MultiplePolarityPragmas xs
    []    -> __IMPOSSIBLE__
  warnUnknownNamesInFixityDecl        = warning   . NicifierIssue . UnknownNamesInFixityDecl
  warnUnknownNamesInPolarityPragmas   = warning   . NicifierIssue . UnknownNamesInPolarityPragmas
  warnUnknownFixityInMixfixDecl       = warning   . NicifierIssue . UnknownFixityInMixfixDecl
  warnPolarityPragmasButNotPostulates = warning   . NicifierIssue . PolarityPragmasButNotPostulates

-- | Collect the fixity/syntax declarations and polarity pragmas from the list
--   of declarations and store them in the scope.
computeFixitiesAndPolarities :: DoWarn -> [C.Declaration] -> ScopeM a -> ScopeM a
computeFixitiesAndPolarities warn ds cont = do
  fp <- fixitiesAndPolarities warn ds
  -- Andreas, 2019-08-16:
  -- Since changing fixities and polarities does not affect the name sets,
  -- we do not need to invoke @modifyScope@ here
  -- (which does @recomputeInverseScopeMaps@).
  -- A simple @locallyScope@ is sufficient.
  locallyScope scopeFixitiesAndPolarities (const fp) cont

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
    PatternSynResName n -> return $ oneNotation n
    UnknownName         -> __IMPOSSIBLE__
  where
    notation = namesToNotation x . qnameName . anameName
    oneNotation ds =
      case mergeNotations $ map notation $ toList ds of
        [n] -> n
        _   -> __IMPOSSIBLE__

---------------------------------------------------------------------------
-- * Binding names
---------------------------------------------------------------------------

-- | Bind a variable.
bindVariable
  :: A.BindingSource -- ^ @λ@, @Π@, @let@, ...?
  -> C.Name          -- ^ Concrete name.
  -> A.Name          -- ^ Abstract name.
  -> ScopeM ()
bindVariable b x y = modifyLocalVars $ AssocList.insert x $ LocalVar y b []

-- | Temporarily unbind a variable. Used for non-recursive lets.
unbindVariable :: C.Name -> ScopeM a -> ScopeM a
unbindVariable x = bracket_ (getLocalVars <* modifyLocalVars (AssocList.delete x)) (modifyLocalVars . const)

-- | Bind a defined name. Must not shadow anything.
bindName :: Access -> KindOfName -> C.Name -> A.QName -> ScopeM ()
bindName acc kind x y = bindName' acc kind NoMetadata x y

bindName' :: Access -> KindOfName -> NameMetadata -> C.Name -> A.QName -> ScopeM ()
bindName' acc kind meta x y = do
  when (isNoName x) $ modifyScopes $ Map.map $ removeNameFromScope PrivateNS x
  r  <- resolveName (C.QName x)
  y' <- case r of
    -- Binding an anonymous declaration always succeeds.
    -- In case it's not the first one, we simply remove the one that came before
    _ | isNoName x      -> success
    DefinedName _ d     -> clash $ anameName d
    VarName z _         -> clash $ A.qualify (mnameFromList []) z
    FieldName       ds  -> ambiguous FldName ds
    ConstructorName ds  -> ambiguous ConName ds
    PatternSynResName n -> ambiguous PatternSynName n
    UnknownName         -> success
  let ns = if isNoName x then PrivateNS else localNameSpace acc
  modifyCurrentScope $ addNameToScope ns x y'
  where
    success = return $ AbsName y kind Defined meta
    clash   = typeError . ClashingDefinition (C.QName x)

    ambiguous k ds =
      if kind == k && all ((== k) . anameKind) ds
      then success else clash $ anameName (headNe ds)

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

---------------------------------------------------------------------------
-- * Module manipulation operations
---------------------------------------------------------------------------

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
      lift $ reportSLn "scope.copy" 20 $ "Copying scope " ++ prettyShow old ++ " to " ++ prettyShow new
      lift $ reportSLn "scope.copy" 50 $ prettyShow s
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
          return $ x { A.nameId = i }

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
          lift $ reportSLn "scope.copy" 50 $ "  Copying " ++ prettyShow x ++ " to " ++ prettyShow y
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
            let newM = if x `isLtChildModuleOf` old then newL else mnameToList new0

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
            lift $ reportSLn "scope.copy" 50 $ "  Copying module " ++ prettyShow x ++ " to " ++ prettyShow y
            addMod x y rec
            lift $ createModule Nothing y
            -- We need to copy the contents of included modules recursively (only when 'rec')
            when rec $ copyRec x y
            return y
          where
            copyRec x y = do
              s0 <- lift $ getNamedScope x
              s  <- withCurrentModule' y $ copy y s0
              lift $ modifyNamedScope y (const s)

---------------------------------------------------------------------------
-- * Import directives
---------------------------------------------------------------------------

-- | Warn about useless fixity declarations in @renaming@ directives.
checkNoFixityInRenamingModule :: [C.Renaming] -> ScopeM ()
checkNoFixityInRenamingModule ren = do
  whenJust (NonemptyList.fromList $ mapMaybe rangeOfUselessInfix ren) $ \ rs -> do
    traceCall (SetRange $ getRange rs) $ do
      warning $ FixityInRenamingModule rs
  where
  rangeOfUselessInfix :: C.Renaming -> Maybe Range
  rangeOfUselessInfix = \case
    Renaming ImportedModule{} _ mfx _ -> getRange <$> mfx
    _ -> Nothing

-- | Apply an import directive and check that all the names mentioned actually
--   exist.
applyImportDirectiveM
  :: C.QName                           -- ^ Name of the scope, only for error reporting.
  -> C.ImportDirective                 -- ^ Description of how scope is to be modified.
  -> Scope                             -- ^ Input scope.
  -> ScopeM (A.ImportDirective, Scope) -- ^ Scope-checked description, output scope.
applyImportDirectiveM m (ImportDirective rng usn' hdn' ren' public) scope = do

    -- Modules names do not come with fixities, thus, we should complain if the
    -- user supplied fixity annotations to renaming-module clauses.
    checkNoFixityInRenamingModule ren'

    -- We start by checking that all of the names talked about in the import
    -- directive do exist.  If some do not then we remove them and raise a warning.
    let usingList = fromUsing usn'
    let (missingExports, namesA) = checkExist $ usingList ++ hdn' ++ map renFrom ren'
    unless (null missingExports) $ setCurrentRange rng $ do
      reportSLn "scope.import.apply" 20 $ "non existing names: " ++ prettyShow missingExports
      warning $ ModuleDoesntExport m missingExports

    -- We can now define a cleaned-up version of the import directive.
    let notMissing = not . (missingExports `hasElem`)  -- #3997, efficient lookup in missingExports
    let usn = filter notMissing usingList        -- remove missingExports from usn'
    let hdn = filter notMissing hdn'             -- remove missingExports from hdn'
    let ren = filter (notMissing . renFrom) ren'                   -- and from ren'
    let dir = ImportDirective rng (mapUsing (const usn) usn') hdn ren public

    -- Convenient shorthands for defined names and names brought into scope:
    let names        = map renFrom ren ++ hdn ++ usn
    let definedNames = map renTo ren
    let targetNames  = usn ++ definedNames

    -- Efficient test of (`elem` names):
    let inNames      = (names `hasElem`)

    -- Efficient test of whether a module import should be added to the import
    -- of a definition (like a data or record definition).
    let extra x = and
          [ inNames       $ ImportedName   x
          , notMissing    $ ImportedModule x
          , not . inNames $ ImportedModule x
              -- The last test implies that @hiding (module M)@ prevents @module M@
              -- from entering the @using@ list in @addExtraModule@.
          ]

    dir' <- sanityCheck (not . inNames) $ addExtraModules extra dir

    -- Check for duplicate imports in a single import directive.
    -- @dup@ : To be imported names that are mentioned more than once.
    unlessNull (allDuplicates targetNames) $ \ dup ->
      typeError $ DuplicateImports m dup

    -- Apply the import directive.
    let (scope', (nameClashes, moduleClashes)) = applyImportDirective_ dir' scope

    -- Andreas, 2019-11-08, issue #4154, report clashes
    -- introduced by the @renaming@.
    unless (null nameClashes) $
      warning $ ClashesViaRenaming NameNotModule $ Set.toList nameClashes
    unless (null moduleClashes) $
      warning $ ClashesViaRenaming ModuleNotName $ Set.toList moduleClashes

    -- Look up the defined names in the new scope.
    let namesInScope'   = (allNamesInScope scope' :: ThingsInScope AbstractName)
    let modulesInScope' = (allNamesInScope scope' :: ThingsInScope AbstractModule)
    let look x = headWithDefault __IMPOSSIBLE__ . Map.findWithDefault __IMPOSSIBLE__ x
    -- We set the ranges to the ranges of the concrete names in order to get
    -- highlighting for the names in the import directive.
    let definedA = for definedNames $ \case
          ImportedName   x -> ImportedName   . (x,) . setRange (getRange x) . anameName $ look x namesInScope'
          ImportedModule x -> ImportedModule . (x,) . setRange (getRange x) . amodName  $ look x modulesInScope'

    let adir = mapImportDir namesA definedA dir
    return (adir, scope') -- TODO Issue 1714: adir

  where
    -- | Names in the @using@ directive
    fromUsing :: Using' a b -> [ImportedName' a b]
    fromUsing = \case
      Using  xs     -> xs
      UseEverything -> []

    -- If both @using@ and @hiding@ directive are present,
    -- the hiding directive may only contain modules whose twins are mentioned.
    sanityCheck notMentioned = \case
      dir@(ImportDirective{ using = Using{}, hiding = ys }) -> do
          let useless = \case
                ImportedName{}   -> True
                ImportedModule y -> notMentioned (ImportedName y)
          unlessNull (filter useless ys) $ \ uselessHiding -> do
            typeError $ GenericError $ unwords $
              [ "Hiding"
              , List.intercalate ", " $ map prettyShow uselessHiding
              , "has no effect"
              ]
          -- We can empty @hiding@ now, since there is an explicit @using@ directive
          -- and @hiding@ served its purpose to prevent modules to enter the @Using@ list.
          return dir{ hiding = [] }
      dir -> return dir

    addExtraModules :: (C.Name -> Bool) -> C.ImportDirective -> C.ImportDirective
    addExtraModules extra dir =
      dir{ using       = mapUsing (concatMap addExtra) $ using dir
         , hiding      = concatMap addExtra            $ hiding dir
         , impRenaming = concatMap extraRenaming       $ impRenaming dir
         }
      where
        addExtra f@(ImportedName y) | extra y = [f, ImportedModule y]
        addExtra m = [m]

        extraRenaming = \case
          r@(Renaming (ImportedName y) (ImportedName z) _fixity rng) | extra y ->
             [ r , Renaming (ImportedModule y) (ImportedModule z) Nothing rng ]
          r -> [r]

    -- | Names and modules (abstract) in scope before the import.
    namesInScope   = (allNamesInScope scope :: ThingsInScope AbstractName)
    modulesInScope = (allNamesInScope scope :: ThingsInScope AbstractModule)

    -- | AST versions of the concrete names passed as an argument.
    --   We get back a pair consisting of a list of missing exports first,
    --   and a list of successful imports second.
    checkExist :: [ImportedName] -> ([ImportedName], [ImportedName' (C.Name, A.QName) (C.Name, A.ModuleName)])
    checkExist xs = partitionEithers $ for xs $ \ name -> case name of
      ImportedName x   -> ImportedName   . (x,) . setRange (getRange x) . anameName <$> resolve name x namesInScope
      ImportedModule x -> ImportedModule . (x,) . setRange (getRange x) . amodName  <$> resolve name x modulesInScope

      where resolve :: Ord a => err -> a -> Map a [b] -> Either err b
            resolve err x m = maybe (Left err) (Right . head) $ Map.lookup x m

-- | Translation of @ImportDirective@.
mapImportDir
  :: (Ord n1, Ord m1)
  => [ImportedName' (n1,n2) (m1,m2)]  -- ^ Translation of imported names.
  -> [ImportedName' (n1,n2) (m1,m2)]  -- ^ Translation of names defined by this import.
  -> ImportDirective' n1 m1
  -> ImportDirective' n2 m2
mapImportDir src0 tgt0 (ImportDirective r u h ren open) =
  ImportDirective r
    (mapUsing (map (lookupImportedName src)) u)
    (map (lookupImportedName src) h)
    (map (mapRenaming src tgt) ren)
    open
  where
  src = importedNameMapFromList src0
  tgt = importedNameMapFromList tgt0

-- | A finite map for @ImportedName@s.

data ImportedNameMap n1 n2 m1 m2 = ImportedNameMap
  { inameMap   :: Map n1 n2
  , imoduleMap :: Map m1 m2
  }

-- | Create a 'ImportedNameMap'.
importedNameMapFromList
  :: (Ord n1, Ord m1)
  => [ImportedName' (n1,n2) (m1,m2)]
  -> ImportedNameMap n1 n2 m1 m2
importedNameMapFromList = foldr (flip add) $ ImportedNameMap Map.empty Map.empty
  where
  add (ImportedNameMap nm mm) = \case
    ImportedName   (x,y) -> ImportedNameMap (Map.insert x y nm) mm
    ImportedModule (x,y) -> ImportedNameMap nm (Map.insert x y mm)

-- | Apply a 'ImportedNameMap'.
lookupImportedName
  :: (Ord n1, Ord m1)
  => ImportedNameMap n1 n2 m1 m2
  -> ImportedName' n1 m1
  -> ImportedName' n2 m2
lookupImportedName (ImportedNameMap nm mm) = \case
    ImportedName   x -> ImportedName   $ Map.findWithDefault __IMPOSSIBLE__ x nm
    ImportedModule x -> ImportedModule $ Map.findWithDefault __IMPOSSIBLE__ x mm

-- | Translation of @Renaming@.
mapRenaming
  ::  (Ord n1, Ord m1)
  => ImportedNameMap n1 n2 m1 m2  -- ^ Translation of 'renFrom' names and module names.
  -> ImportedNameMap n1 n2 m1 m2  -- ^ Translation of 'rento'   names and module names.
  -> Renaming' n1 m1  -- ^ Renaming before translation (1).
  -> Renaming' n2 m2  -- ^ Renaming after  translation (2).
mapRenaming src tgt (Renaming from to fixity r) =
  Renaming (lookupImportedName src from) (lookupImportedName tgt to) fixity r

---------------------------------------------------------------------------
-- * Opening a module
---------------------------------------------------------------------------

data OpenKind = LetOpenModule | TopOpenModule

noGeneralizedVarsIfLetOpen :: OpenKind -> Scope -> Scope
noGeneralizedVarsIfLetOpen TopOpenModule = id
noGeneralizedVarsIfLetOpen LetOpenModule = disallowGeneralizedVars

-- | Open a module.
openModule_ :: OpenKind -> C.QName -> C.ImportDirective -> ScopeM A.ImportDirective
openModule_ kind cm dir = openModule kind Nothing cm dir

-- | Open a module, possibly given an already resolved module name.
openModule :: OpenKind -> Maybe A.ModuleName  -> C.QName -> C.ImportDirective -> ScopeM A.ImportDirective
openModule kind mam cm dir = do
  current <- getCurrentModule
  m <- caseMaybe mam (amodName <$> resolveModule cm) return
  let acc | Nothing <- publicOpen dir     = PrivateNS
          | m `isLtChildModuleOf` current = PublicNS
          | otherwise                     = ImportedNS

  -- Get the scope exported by module to be opened.
  (adir, s') <- applyImportDirectiveM cm dir . inScopeBecause (Opened cm) .
                noGeneralizedVarsIfLetOpen kind .
                removeOnlyQualified . restrictPrivate =<< getNamedScope m
  let s  = setScopeAccess acc s'
  let ns = scopeNameSpace acc s
  modifyCurrentScope (`mergeScope` s)
  -- Andreas, 2018-06-03, issue #3057:
  -- If we simply check for ambiguous exported identifiers _after_
  -- importing the new identifiers into the current scope, we also
  -- catch the case of importing an ambiguous identifier.
  checkForClashes

  -- Importing names might shadow existing locals.
  verboseS "scope.locals" 10 $ do
    locals <- mapMaybe (\ (c,x) -> c <$ notShadowedLocal x) <$> getLocalVars
    let newdefs = Map.keys $ nsNames ns
        shadowed = List.intersect locals newdefs
    reportSLn "scope.locals" 10 $ "opening module shadows the following locals vars: " ++ prettyShow shadowed
  -- Andreas, 2014-09-03, issue 1266: shadow local variables by imported defs.
  modifyLocalVars $ AssocList.mapWithKey $ \ c x ->
    case Map.lookup c $ nsNames ns of
      Nothing -> x
      Just ys -> shadowLocal ys x

  return adir

  where
    -- Only checks for clashes that would lead to the same
    -- name being exported twice from the module.
    checkForClashes = when (isJust $ publicOpen dir) $ do

        exported <- allThingsInScope . restrictPrivate <$> (getNamedScope =<< getCurrentModule)

        -- Get all exported concrete names that are mapped to at least 2 abstract names
        let defClashes = filter (\ (_c, as) -> length as >= 2) $ Map.toList $ nsNames exported
            modClashes = filter (\ (_c, as) -> length as >= 2) $ Map.toList $ nsModules exported

            -- No ambiguity if concrete identifier is only mapped to
            -- constructor names or only to projection names.
            defClash (_, qs) = not $ all (== ConName) ks || all (==FldName) ks
              where ks = map anameKind qs
        -- We report the first clashing exported identifier.
        unlessNull (filter (\ x -> defClash x) defClashes) $
          \ ((x, q:_) : _) -> typeError $ ClashingDefinition (C.QName x) $ anameName q

        unlessNull modClashes $ \ ((_, ms) : _) -> do
          caseMaybe (last2 ms) __IMPOSSIBLE__ $ \ (m0, m1) -> do
            typeError $ ClashingModule (amodName m0) (amodName m1)
