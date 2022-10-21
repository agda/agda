{-# LANGUAGE NondecreasingIndentation #-}

{-| The scope monad with operations.
-}

module Agda.Syntax.Scope.Monad where

import Prelude hiding (null)

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.Except
import Control.Monad.State

import Data.Either ( partitionEithers )
import Data.Foldable (all, traverse_)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable hiding (for)

import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract (ScopeCopyInfo(..))
import Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Fixity
import Agda.Syntax.Concrete.Definitions ( DeclarationWarning(..) ,DeclarationWarning'(..) )
  -- TODO: move the relevant warnings out of there
import Agda.Syntax.Scope.Base as A

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin ( HasBuiltins , getBuiltinName' , builtinSet , builtinProp , builtinSetOmega, builtinSSetOmega )
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Positivity.Occurrence (Occurrence)
import Agda.TypeChecking.Warnings ( warning, warning' )

import qualified Agda.Utils.AssocList as AssocList
import Agda.Utils.CallStack ( CallStack, HasCallStack, withCallerCallStack )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1 (List1, pattern (:|), nonEmpty, toList)
import Agda.Utils.List2 (List2(List2), toList)
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.List2 as List2
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.Singleton
import Agda.Utils.Suffix as C

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

scopeWarning' :: CallStack -> DeclarationWarning' -> ScopeM ()
scopeWarning' loc = warning' loc . NicifierIssue . DeclarationWarning loc

scopeWarning :: HasCallStack => DeclarationWarning' -> ScopeM ()
scopeWarning = withCallerCallStack scopeWarning'

---------------------------------------------------------------------------
-- * General operations
---------------------------------------------------------------------------

isDatatypeModule :: ReadTCState m => A.ModuleName -> m (Maybe DataOrRecordModule)
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
--   If the module is not new (e.g. duplicate @import@),
--   don't erase its contents.
--   (@Just@ if it is a datatype or record module.)
createModule :: Maybe DataOrRecordModule -> A.ModuleName -> ScopeM ()
createModule b m = do
  reportSLn "scope.createModule" 10 $ "createModule " ++ prettyShow m
  s <- getCurrentScope
  let parents = scopeName s : scopeParents s
      sm = emptyScope { scopeName           = m
                      , scopeParents        = parents
                      , scopeDatatypeModule = b }
  -- Andreas, 2015-07-02: internal error if module is not new.
  -- Ulf, 2016-02-15: It's not new if multiple imports (#1770).
  -- Andreas, 2020-05-18, issue #3933:
  -- If it is not new (but apparently did not clash),
  -- we do not erase its contents for reasons of monotonicity.
  modifyScopes $ Map.insertWith mergeScope m sm

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

-- | Run a computation outside some number of local variables and add them back afterwards. This
--   lets you bind variables in the middle of the context and is used when binding generalizable
--   variables (#3735).
outsideLocalVars :: Int -> ScopeM a -> ScopeM a
outsideLocalVars n m = do
  inner <- take n <$> getLocalVars
  modifyLocalVars (drop n)
  x <- m
  modifyLocalVars (inner ++)
  return x

-- | Check that the newly added variable have unique names.

withCheckNoShadowing :: ScopeM a -> ScopeM a
withCheckNoShadowing = bracket_ getLocalVars $ \ lvarsOld ->
  checkNoShadowing lvarsOld =<< getLocalVars

checkNoShadowing :: LocalVars  -- ^ Old local scope
                 -> LocalVars  -- ^ New local scope
                 -> ScopeM ()
checkNoShadowing old new = do
  opts <- pragmaOptions
  when (ShadowingInTelescope_ `Set.member`
          (optWarningMode opts ^. warningSet)) $ do
    -- LocalVars is currnently an AssocList so the difference between
    -- two local scope is the left part of the new one.
    let diff = dropEnd (length old) new
    -- Filter out the underscores.
    let newNames = filter (not . isNoName) $ AssocList.keys diff
    -- Associate each name to its occurrences.
    let nameOccs1 :: [(C.Name, List1 Range)]
        nameOccs1 = Map.toList $ Map.fromListWith (<>) $ map pairWithRange newNames
    -- Warn if we have two or more occurrences of the same name.
    let nameOccs2 :: [(C.Name, List2 Range)]
        nameOccs2 = mapMaybe (traverseF List2.fromList1Maybe) nameOccs1
    caseList nameOccs2 (return ()) $ \ c conflicts -> do
      scopeWarning $ ShadowingInTelescope $ c :| conflicts
  where
    pairWithRange :: C.Name -> (C.Name, List1 Range)
    pairWithRange n = (n, singleton $ getRange n)

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

annotateDecls :: ReadTCState m => m [A.Declaration] -> m A.Declaration
annotateDecls m = do
  ds <- m
  s  <- getScope
  return $ A.ScopedDecl s ds

annotateExpr :: ReadTCState m => m A.Expr -> m A.Expr
annotateExpr m = do
  e <- m
  s <- getScope
  return $ A.ScopedExpr s e

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
    , nameCanonical   = x
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
-- | NOTE: See @chooseName@ in @Agda.Syntax.Translation.AbstractToConcrete@ for similar logic.
-- | NOTE: See @withName@ in @Agda.Syntax.Translation.ReflectedToAbstract@ for similar logic.
freshConcreteName :: Range -> Int -> String -> ScopeM C.Name
freshConcreteName r i s = do
  let cname = C.Name r C.NotInScope $ singleton $ Id $ stringToRawName $ s ++ show i
  resolveName (C.QName cname) >>= \case
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
  Left reason  -> do
    reportS "scope.resolve" 60 $ unlines $
      "resolveName': ambiguous name" :
      map (show . qnameName) (toList $ ambiguousNamesInReason reason)
    setCurrentRange x $ typeError $ AmbiguousName x reason
  Right x' -> return x'

tryResolveName
  :: forall m. (ReadTCState m, HasBuiltins m, MonadError AmbiguousNameReason m)
  => KindsOfNames       -- ^ Restrict search to these kinds of names.
  -> Maybe (Set A.Name) -- ^ Unless 'Nothing', restrict search to match any of these names.
  -> C.QName            -- ^ Name to be resolved
  -> m ResolvedName     -- ^ If illegally ambiguous, throw error with the ambiguous name.
tryResolveName kinds names x = do
  scope <- getScope
  let vars     = AssocList.mapKeysMonotonic C.QName $ scope ^. scopeLocals
  case lookup x vars of

    -- Case: we have a local variable x, but is (perhaps) shadowed by some imports ys.
    Just var@(LocalVar y b ys) ->
      -- We may ignore the imports filtered out by the @names@ filter.
      case nonEmpty $ filterNames id ys of
        Nothing  -> return $ VarName y{ nameConcrete = unqualify x } b
        Just ys' -> throwError $ AmbiguousLocalVar var ys'

    -- Case: we do not have a local variable x.
    Nothing -> do
      -- Consider only names that are in the given set of names and
      -- are of one of the given kinds
      let filtKind = filter $ (`elemKindsOfNames` kinds) . anameKind . fst
          possibleNames z = filtKind $ filterNames fst $ scopeLookup' z scope
      -- If the name has a suffix, also consider the possibility that
      -- the base name is in scope (e.g. the builtin sorts `Set` and `Prop`).
      canHaveSuffix <- canHaveSuffixTest
      let (xsuffix, xbase) = (C.lensQNameName . nameSuffix) (,Nothing) x
          possibleBaseNames = filter (canHaveSuffix . anameName . fst) $ possibleNames xbase
          suffixedNames = (,) <$> fromConcreteSuffix xsuffix <*> nonEmpty possibleBaseNames
      case (nonEmpty $ possibleNames x) of
        Just ds  | let ks = fmap (isConName . anameKind . fst) ds
                 , all isJust ks
                 , isNothing suffixedNames ->
          return $ ConstructorName (Set.fromList $ List1.catMaybes ks) $ fmap (upd . fst) ds

        Just ds  | all ((FldName ==) . anameKind . fst) ds , isNothing suffixedNames ->
          return $ FieldName $ fmap (upd . fst) ds

        Just ds  | all ((PatternSynName ==) . anameKind . fst) ds , isNothing suffixedNames ->
          return $ PatternSynResName $ fmap (upd . fst) ds

        Just ((d, a) :| ds) -> case (suffixedNames, ds) of
          (Nothing, []) ->
            return $ DefinedName a (upd d) A.NoSuffix
          (Nothing, (d',_) : ds') ->
            throwError $ AmbiguousDeclName $ List2 d d' $ map fst ds'
          (Just (_, ss), _) ->
            throwError $ AmbiguousDeclName $ List2.append (d :| map fst ds) (fmap fst ss)

        Nothing -> case suffixedNames of
          Nothing -> return UnknownName
          Just (suffix , (d, a) :| []) -> return $ DefinedName a (upd d) suffix
          Just (suffix , (d1,_) :| (d2,_) : sds) ->
            throwError $ AmbiguousDeclName $ List2 d1 d2 $ map fst sds

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
  fromConcreteSuffix = \case
    Nothing              -> Nothing
    Just C.Prime{}       -> Nothing
    Just (C.Index i)     -> Just $ A.Suffix i
    Just (C.Subscript i) -> Just $ A.Suffix i

-- | Test if a given abstract name can appear with a suffix. Currently
--   only true for the names of builtin sorts @Set@ and @Prop@.
canHaveSuffixTest :: HasBuiltins m => m (A.QName -> Bool)
canHaveSuffixTest = do
  builtinSet  <- getBuiltinName' builtinSet
  builtinProp <- getBuiltinName' builtinProp
  builtinSetOmega <- getBuiltinName' builtinSetOmega
  builtinSSetOmega <- getBuiltinName' builtinSSetOmega
  return $ \x -> Just x `elem` [builtinSet, builtinProp, builtinSetOmega, builtinSSetOmega]

-- | Look up a module in the scope.
resolveModule :: C.QName -> ScopeM AbstractModule
resolveModule x = do
  ms <- scopeLookup x <$> getScope
  caseMaybe (nonEmpty ms) (typeError $ NoSuchModule x) $ \ case
    AbsModule m why :| [] -> return $ AbsModule (m `withRangeOf` x) why
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
  warnUnknownNamesInFixityDecl        = scopeWarning . UnknownNamesInFixityDecl
  warnUnknownNamesInPolarityPragmas   = scopeWarning . UnknownNamesInPolarityPragmas
  warnUnknownFixityInMixfixDecl       = scopeWarning . UnknownFixityInMixfixDecl
  warnPolarityPragmasButNotPostulates = scopeWarning . PolarityPragmasButNotPostulates

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
    DefinedName _ d _   -> return $ notation d
    FieldName ds        -> return $ oneNotation ds
    ConstructorName _ ds-> return $ oneNotation ds
    PatternSynResName n -> return $ oneNotation n
    UnknownName         -> __IMPOSSIBLE__
  where
    notation = namesToNotation x . qnameName . anameName
    oneNotation ds =
      case mergeNotations $ map notation $ List1.toList ds of
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
bindName' acc kind meta x y = whenJustM (bindName'' acc kind meta x y) typeError

-- | Bind a name. Returns the 'TypeError' if exists, but does not throw it.
bindName'' :: Access -> KindOfName -> NameMetadata -> C.Name -> A.QName -> ScopeM (Maybe TypeError)
bindName'' acc kind meta x y = do
  when (isNoName x) $ modifyScopes $ Map.map $ removeNameFromScope PrivateNS x
  r  <- resolveName (C.QName x)
  let y' :: Either TypeError AbstractName
      y' = case r of
        -- Binding an anonymous declaration always succeeds.
        -- In case it's not the first one, we simply remove the one that came before
        _ | isNoName x      -> success
        DefinedName _ d _   -> clash $ anameName d
        VarName z _         -> clash $ A.qualify_ z
        FieldName       ds  -> ambiguous (== FldName) ds
        ConstructorName i ds-> ambiguous (isJust . isConName) ds
        PatternSynResName n -> ambiguous (== PatternSynName) n
        UnknownName         -> success
  let ns = if isNoName x then PrivateNS else localNameSpace acc
  traverse_ (modifyCurrentScope . addNameToScope ns x) y'
  pure $ either Just (const Nothing) y'
  where
    success = Right $ AbsName y kind Defined meta
    clash n = Left $ ClashingDefinition (C.QName x) n Nothing

    ambiguous f ds =
      if f kind && all (f . anameKind) ds
      then success else clash $ anameName (List1.head ds)

-- | Rebind a name. Use with care!
--   Ulf, 2014-06-29: Currently used to rebind the name defined by an
--   unquoteDecl, which is a 'QuotableName' in the body, but a 'DefinedName'
--   later on.
rebindName :: Access -> KindOfName -> C.Name -> A.QName -> ScopeM ()
rebindName acc kind x y = do
  if kind == ConName
    then modifyCurrentScope $
           mapScopeNS (localNameSpace acc)
                      (Map.update (toList <.> nonEmpty . (filter ((==) ConName . anameKind))) x)
                      id
                      id
    else modifyCurrentScope $ removeNameFromScope (localNameSpace acc) x
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
  , memoModules :: Map ModuleName (ModuleName, Bool)
    -- ^ Bool: did we copy recursively? We need to track this because we don't
    --   copy recursively when creating new modules for reexported functions
    --   (issue1985), but we might need to copy recursively later.
  }

memoToScopeInfo :: ScopeMemo -> ScopeCopyInfo
memoToScopeInfo (ScopeMemo names mods) =
  ScopeCopyInfo { renNames   = names
                , renModules = Map.map (pure . fst) mods }

-- | Create a new scope with the given name from an old scope. Renames
--   public names in the old scope to match the new name and returns the
--   renamings.
copyScope :: C.QName -> A.ModuleName -> Scope -> ScopeM (Scope, ScopeCopyInfo)
copyScope oldc new0 s = (inScopeBecause (Applied oldc) *** memoToScopeInfo) <$> runStateT (copy new0 s) (ScopeMemo mempty mempty)
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
        addName x y     = modify $ \ i -> i { memoNames   = Map.insertWith (<>) x (pure y) (memoNames i) }
        addMod  x y rec = modify $ \ i -> i { memoModules = Map.insert x (y, rec) (memoModules i) }

        -- Querying the memo structure.
        findName x = gets (Map.lookup x . memoNames) -- NB:: Defined but not used
        findMod  x = gets (Map.lookup x . memoModules)

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
          m <- if x `isInModule` old
                 then return new'
                 else renMod' False (qnameModule x)
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
               y <- refresh $ lastWithDefault __IMPOSSIBLE__ $ A.mnameToList x
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
--   Monadic for the sake of error reporting.
checkNoFixityInRenamingModule :: [C.Renaming] -> ScopeM ()
checkNoFixityInRenamingModule ren = do
  whenJust (nonEmpty $ mapMaybe rangeOfUselessInfix ren) $ \ rs -> do
    setCurrentRange rs $ do
      warning $ FixityInRenamingModule rs
  where
  rangeOfUselessInfix :: C.Renaming -> Maybe Range
  rangeOfUselessInfix = \case
    Renaming ImportedModule{} _ mfx _ -> getRange <$> mfx
    _ -> Nothing

-- Moved here carefully from Parser.y to preserve the archaeological artefact
-- dating from Oct 2005 (5ba14b647b9bd175733f9563e744176425c39126).
-- | Check that an import directive doesn't contain repeated names.
verifyImportDirective :: [C.ImportedName] -> C.HidingDirective -> C.RenamingDirective -> ScopeM ()
verifyImportDirective usn hdn ren =
    case filter ((>1) . length)
         $ List.group
         $ List.sort xs
    of
        []  -> return ()
        yss -> setCurrentRange yss $ genericError $
                "Repeated name" ++ s ++ " in import directive: " ++
                concat (List.intersperse ", " $ map (prettyShow . head) yss)
            where
                s = case yss of
                        [_] -> ""
                        _   -> "s"
    where
        xs = usn ++ hdn ++ map renFrom ren

-- | Apply an import directive and check that all the names mentioned actually
--   exist.
--
--   Monadic for the sake of error reporting.
applyImportDirectiveM
  :: C.QName                           -- ^ Name of the scope, only for error reporting.
  -> C.ImportDirective                 -- ^ Description of how scope is to be modified.
  -> Scope                             -- ^ Input scope.
  -> ScopeM (A.ImportDirective, Scope) -- ^ Scope-checked description, output scope.
applyImportDirectiveM m (ImportDirective rng usn' hdn' ren' public) scope0 = do

    -- Module names do not come with fixities, thus, we should complain if the
    -- user has supplied fixity annotations to @renaming module@ clauses.
    checkNoFixityInRenamingModule ren'

    -- Andreas, 2020-06-06, issue #4707
    -- Duplicates in @using@ directive are dropped with a warning.
    usingList <- discardDuplicatesInUsing usn'

    -- The following check was originally performed by the parser.
    -- The Great Ulf Himself added the check back in the dawn of time
    -- (5ba14b647b9bd175733f9563e744176425c39126)
    -- when Agda 2 wasn't even believed to exist yet.
    verifyImportDirective usingList hdn' ren'

    -- We start by checking that all of the names talked about in the import
    -- directive do exist.  If some do not then we remove them and raise a warning.
    let (missingExports, namesA) = checkExist $ usingList ++ hdn' ++ map renFrom ren'
    unless (null missingExports) $ setCurrentRange rng $ do
      reportSLn "scope.import.apply" 20 $ "non existing names: " ++ prettyShow missingExports
      warning $ ModuleDoesntExport m (Map.keys namesInScope) (Map.keys modulesInScope) missingExports

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
    let extra x = inNames (ImportedName   x)
               && notMissing (ImportedModule x)
               && (not . inNames $ ImportedModule x)
                  -- The last test implies that @hiding (module M)@ prevents @module M@
                  -- from entering the @using@ list in @addExtraModule@.

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
    -- Andreas, 2020-06-23, issue #4773, fixing regression in 2.5.1.
    -- Import directive may not mention private things.
    -- ```agda
    --   module M where private X = Set
    --   module N = M using (X)
    -- ```
    -- Further, modules (N) need not copy private things (X) from other
    -- modules (M) ever, since they cannot legally referred to
    -- (neither through qualification (N.X) nor open N).
    -- Thus, we can unconditionally remove private definitions
    -- before we apply the import directive.
    scope = restrictPrivate scope0

    -- Return names in the @using@ directive, discarding duplicates.
    -- Monadic for the sake of throwing warnings.
    discardDuplicatesInUsing :: C.Using -> ScopeM [C.ImportedName]
    discardDuplicatesInUsing = \case
      UseEverything -> return []
      Using  xs     -> do
        let (ys, dups) = nubAndDuplicatesOn id xs
        List1.unlessNull dups $ warning . DuplicateUsing
        return ys

    -- If both @using@ and @hiding@ directive are present,
    -- the hiding directive may only contain modules whose twins are mentioned.
    -- Monadic for the sake of error reporting.
    sanityCheck notMentioned = \case
      dir@(ImportDirective{ using = Using{}, hiding = ys }) -> do
          let useless = \case
                ImportedName{}   -> True
                ImportedModule y -> notMentioned (ImportedName y)
          unlessNull (filter useless ys) $ warning . UselessHiding
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

    -- Names and modules (abstract) in scope before the import.
    namesInScope   = (allNamesInScope scope :: ThingsInScope AbstractName)
    modulesInScope = (allNamesInScope scope :: ThingsInScope AbstractModule)
    concreteNamesInScope = (Map.keys namesInScope ++ Map.keys modulesInScope :: [C.Name])

    -- AST versions of the concrete names passed as an argument.
    -- We get back a pair consisting of a list of missing exports first,
    -- and a list of successful imports second.
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
                noGeneralizedVarsIfLetOpen kind =<< getNamedScope m
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
        shadowed = locals `List.intersect` newdefs
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
            -- constructor names or only to projection names or only to pattern synonyms.
            defClash (_, qs) = not $ or
              [ all (isJust . isConName) ks
              , all (== FldName)         ks
              , all (== PatternSynName)  ks
              ]
              where ks = map anameKind qs
        -- We report the first clashing exported identifier.
        unlessNull (filter defClash defClashes) $
          \ ((x, q:_) : _) -> typeError $ ClashingDefinition (C.QName x) (anameName q) Nothing

        unlessNull modClashes $ \ ((_, ms) : _) -> do
          caseMaybe (last2 ms) __IMPOSSIBLE__ $ \ (m0, m1) -> do
            typeError $ ClashingModule (amodName m0) (amodName m1)
