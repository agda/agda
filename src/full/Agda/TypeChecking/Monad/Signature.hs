{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Monad.Signature where

import Prelude hiding (null)

import qualified Control.Monad.Fail as Fail

import Control.Arrow                 ( first, second )
import Control.Monad.Except          ( ExceptT )
import Control.Monad.State           ( StateT  )
import Control.Monad.Reader          ( ReaderT )
import Control.Monad.Writer          ( WriterT )
import Control.Monad.Trans.Maybe     ( MaybeT  )
import Control.Monad.Trans.Identity  ( IdentityT )
import Control.Monad.Trans           ( MonadTrans, lift )

import Data.Foldable (for_)
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import Data.Maybe
import Data.Semigroup ((<>))

import Agda.Interaction.Options

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Abstract (Ren, ScopeCopyInfo(..))
import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Names
import Agda.Syntax.Position
import Agda.Syntax.Treeless (Compiled(..), TTerm, ArgUsage)

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Constraints
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.Mutual
import Agda.TypeChecking.Monad.Open
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.DropArgs
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Coverage.SplitTree
import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Compile
import {-# SOURCE #-} Agda.TypeChecking.Polarity
import {-# SOURCE #-} Agda.TypeChecking.Pretty
import {-# SOURCE #-} Agda.TypeChecking.ProjectionLike
import {-# SOURCE #-} Agda.TypeChecking.Reduce
import {-# SOURCE #-} Agda.TypeChecking.Opacity

import {-# SOURCE #-} Agda.Compiler.Treeless.Erase
import {-# SOURCE #-} Agda.Compiler.Builtin

import Agda.Utils.CallStack.Base
import Agda.Utils.Either
import Agda.Utils.Function ( applyWhen )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import qualified Agda.Utils.List1 as List1
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty (Doc, prettyShow)
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Update

import Agda.Utils.Impossible

-- | If the first argument is @'Erased' something@, then hard
-- compile-time mode is enabled when the continuation is run.

setHardCompileTimeModeIfErased
  :: Erased
  -> TCM a
     -- ^ Continuation.
  -> TCM a
setHardCompileTimeModeIfErased erased =
  localTC
    $ applyWhen (isErased erased) (set eHardCompileTimeMode True)
    . over eQuantity (`composeQuantity` asQuantity erased)

-- | If the quantity is \"erased\", then hard compile-time mode is
-- enabled when the continuation is run.
--
-- Precondition: The quantity must not be @'Quantity1' something@.

setHardCompileTimeModeIfErased'
  :: LensQuantity q
  => q
     -- ^ The quantity.
  -> TCM a
     -- ^ Continuation.
  -> TCM a
setHardCompileTimeModeIfErased' =
  setHardCompileTimeModeIfErased .
    fromMaybe __IMPOSSIBLE__ . erasedFromQuantity . getQuantity

-- | Use run-time mode in the continuation unless the current mode is
-- the hard compile-time mode.

setRunTimeModeUnlessInHardCompileTimeMode
  :: TCM a
     -- ^ Continuation.
  -> TCM a
setRunTimeModeUnlessInHardCompileTimeMode c =
  ifM (viewTC eHardCompileTimeMode) c $
  localTC (over eQuantity $ mapQuantity (`addQuantity` topQuantity)) c

-- | Use hard compile-time mode in the continuation if the first
-- argument is @'Erased' something@. Use run-time mode if the first
-- argument is @'NotErased' something@ and the current mode is not
-- hard compile-time mode.

setModeUnlessInHardCompileTimeMode
  :: Erased
  -> TCM a
     -- ^ Continuation.
  -> TCM a
setModeUnlessInHardCompileTimeMode erased c = case erased of
  Erased{}    -> setHardCompileTimeModeIfErased erased c
  NotErased{} -> do
    warnForPlentyInHardCompileTimeMode erased
    setRunTimeModeUnlessInHardCompileTimeMode c

-- | Warn if the user explicitly wrote @@ω@ or @@plenty@ but the
-- current mode is the hard compile-time mode.

warnForPlentyInHardCompileTimeMode :: Erased -> TCM ()
warnForPlentyInHardCompileTimeMode = \case
  Erased{}    -> return ()
  NotErased o -> do
    let warn = warning $ PlentyInHardCompileTimeMode o
    hard <- viewTC eHardCompileTimeMode
    if not hard then return () else case o of
      QωInferred{} -> return ()
      Qω{}         -> warn
      QωPlenty{}   -> warn

-- | Add a constant to the signature. Lifts the definition to top level.
addConstant :: QName -> Definition -> TCM ()
addConstant q d = do
  reportSDoc "tc.signature" 20 $ "adding constant " <+> pretty q <+> " to signature"

  -- Every constant that gets added to the signature in hard
  -- compile-time mode is treated as erased.
  hard <- viewTC eHardCompileTimeMode
  d    <- if not hard then return d else do
    case erasedFromQuantity (getQuantity d) of
      Nothing     -> __IMPOSSIBLE__
      Just erased -> do
        warnForPlentyInHardCompileTimeMode erased
        return $ mapQuantity (zeroQuantity `composeQuantity`) d

  tel <- getContextTelescope
  let tel' = replaceEmptyName "r" $ killRange $ case theDef d of
              Constructor{} -> fmap hideOrKeepInstance tel
              Function{ funProjection = Right Projection{ projProper = Just{}, projIndex = n } } ->
                let fallback = fmap hideOrKeepInstance tel in
                if n > 0 then fallback else
                -- if the record value is part of the telescope, its hiding should left unchanged
                  case initLast $ telToList tel of
                    Nothing -> fallback
                    Just (doms, dom) -> telFromList $ fmap hideOrKeepInstance doms ++ [dom]
              _ -> tel
  let d' = abstract tel' $ d { defName = q }
  reportSDoc "tc.signature" 60 $ "lambda-lifted definition =" <?> pretty d'
  modifySignature $ updateDefinitions $ HMap.insertWith (+++) q d'
  i <- currentOrFreshMutualBlock
  setMutualBlock i q
  where
    new +++ old = new { defDisplay = defDisplay new ++ defDisplay old
                      , defInstance = defInstance new `mplus` defInstance old }

-- | A combination of 'addConstant' and 'defaultDefn'. The 'Language'
-- does not need to be supplied.

addConstant' ::
  QName -> ArgInfo -> QName -> Type -> Defn -> TCM ()
addConstant' q info x t def = do
  lang <- getLanguage
  addConstant q $ defaultDefn info x t lang def

-- | Set termination info of a defined function symbol.
setTerminates :: MonadTCState m => QName -> Bool -> m ()
setTerminates q b = modifySignature $ updateDefinition q $ updateTheDef $ \case
    def@Function{} -> def { funTerminates = Just b }
    def@Record{}   -> def { recTerminates = Just b }
    def -> def

-- | Set CompiledClauses of a defined function symbol.
setCompiledClauses :: QName -> CompiledClauses -> TCM ()
setCompiledClauses q cc = modifySignature $ updateDefinition q $ updateTheDef $ setT
  where
    setT def@Function{} = def { funCompiled = Just cc }
    setT def            = def

-- | Set SplitTree of a defined function symbol.
setSplitTree :: QName -> SplitTree -> TCM ()
setSplitTree q st = modifySignature $ updateDefinition q $ updateTheDef $ setT
  where
    setT def@Function{} = def { funSplitTree = Just st }
    setT def            = def

-- | Modify the clauses of a function.
modifyFunClauses :: QName -> ([Clause] -> [Clause]) -> TCM ()
modifyFunClauses q f =
  modifySignature $ updateDefinition q $ updateTheDef $ updateFunClauses f

-- | Lifts clauses to the top-level and adds them to definition.
--   Also adjusts the 'funCopatternLHS' field if necessary.
addClauses :: (MonadConstraint m, MonadTCState m) => QName -> [Clause] -> m ()
addClauses q cls = do
  tel <- getContextTelescope
  modifySignature $ updateDefinition q $
    updateTheDef (updateFunClauses (++ abstract tel cls))
    . updateDefCopatternLHS (|| isCopatternLHS cls)

  -- Jesper, 2022-10-13: unblock any constraints that were
  -- waiting for more clauses of this function
  wakeConstraints' $ wakeIfBlockedOnDef q . constraintUnblocker

mkPragma :: String -> TCM CompilerPragma
mkPragma s = CompilerPragma <$> getCurrentRange <*> pure s

-- | Add a compiler pragma `{-\# COMPILE <backend> <name> <text> \#-}`
addPragma :: BackendName -> QName -> String -> TCM ()
addPragma b q s = ifM erased
  {- then -} (warning $ PragmaCompileErased b q)
  {- else -} $ do
    pragma <- mkPragma s
    modifySignature $ updateDefinition q $ addCompilerPragma b pragma

  where

  erased :: TCM Bool
  erased = do
    def <- theDef <$> getConstInfo q
    case def of
      -- If we have a defined symbol, we check whether it is erasable
      Function{} ->
        locallyTC      eActiveBackendName (const $ Just b) $
        locallyTCState stBackends         (const $ builtinBackends) $
        isErasable q
     -- Otherwise (Axiom, Datatype, Record type, etc.) we keep it
      _ -> pure False

getUniqueCompilerPragma :: BackendName -> QName -> TCM (Maybe CompilerPragma)
getUniqueCompilerPragma backend q = do
  ps <- defCompilerPragmas backend <$> getConstInfo q
  case ps of
    []  -> return Nothing
    [p] -> return $ Just p
    (_:p1:_) ->
      setCurrentRange p1 $
            genericDocError =<< do
                  hang (text ("Conflicting " ++ backend ++ " pragmas for") <+> pretty q <+> "at") 2 $
                       vcat [ "-" <+> pretty (getRange p) | p <- ps ]

setFunctionFlag :: FunctionFlag -> Bool -> QName -> TCM ()
setFunctionFlag flag val q = modifyGlobalDefinition q $ set (lensTheDef . funFlag flag) val

markStatic :: QName -> TCM ()
markStatic = setFunctionFlag FunStatic True

markInline :: Bool -> QName -> TCM ()
markInline b = setFunctionFlag FunInline b

markInjective :: QName -> TCM ()
markInjective q = modifyGlobalDefinition q $ \def -> def { defInjective = True }

unionSignatures :: [Signature] -> Signature
unionSignatures ss = foldr unionSignature emptySignature ss
  where
    unionSignature (Sig a b c) (Sig a' b' c') =
      Sig (Map.union a a')
          (HMap.union b b')              -- definitions are unique (in at most one module)
          (HMap.unionWith mappend c c')  -- rewrite rules are accumulated

-- | Add a section to the signature.
--
--   The current context will be stored as the cumulative module parameters
--   for this section.
addSection :: ModuleName -> TCM ()
addSection m = do
  tel <- getContextTelescope
  let sec = Section tel
  -- Make sure we do not overwrite an existing section!
  whenJustM (getSection m) $ \ sec' -> do
    -- At least not with different content!
    if (sec == sec') then do
      -- Andreas, 2015-12-02: test/Succeed/Issue1701II.agda
      -- reports a "redundantly adding existing section".
      reportSDoc "tc.section" 10 $ "warning: redundantly adding existing section" <+> pretty m
      reportSDoc "tc.section" 60 $ "with content" <+> pretty sec
    else do
      reportSDoc "impossible" 10 $ "overwriting existing section" <+> pretty m
      reportSDoc "impossible" 60 $ "of content  " <+> pretty sec'
      reportSDoc "impossible" 60 $ "with content" <+> pretty sec
      __IMPOSSIBLE__
  -- Add the new section.
  setModuleCheckpoint m
  modifySignature $ over sigSections $ Map.insert m sec

-- | Sets the checkpoint for the given module to the current checkpoint.
setModuleCheckpoint :: ModuleName -> TCM ()
setModuleCheckpoint m = do
  chkpt <- viewTC eCurrentCheckpoint
  stModuleCheckpoints `modifyTCLens` Map.insert m chkpt

-- | Get a section.
--
--   Why Maybe? The reason is that we look up all prefixes of a module to
--   compute number of parameters, and for hierarchical top-level modules,
--   A.B.C say, A and A.B do not exist.
{-# SPECIALIZE getSection :: ModuleName -> TCM (Maybe Section) #-}
{-# SPECIALIZE getSection :: ModuleName -> ReduceM (Maybe Section) #-}
getSection :: (Functor m, ReadTCState m) => ModuleName -> m (Maybe Section)
getSection m = do
  sig  <- (^. stSignature . sigSections) <$> getTCState
  isig <- (^. stImports   . sigSections) <$> getTCState
  return $ Map.lookup m sig `mplus` Map.lookup m isig

-- | Lookup a section telescope.
--
--   If it doesn't exist, like in hierarchical top-level modules,
--   the section telescope is empty.
{-# SPECIALIZE lookupSection :: ModuleName -> TCM Telescope #-}
{-# SPECIALIZE lookupSection :: ModuleName -> ReduceM Telescope #-}
lookupSection :: (Functor m, ReadTCState m) => ModuleName -> m Telescope
lookupSection m = maybe EmptyTel (^. secTelescope) <$> getSection m

-- | Add display forms for a name @f@ copied by a module application. Essentially if @f@ can reduce to
--
-- @
-- λ xs → A.B.C.f vs
-- @
--
-- by unfolding module application copies (`defCopy`), then we add a display form
--
-- @
-- A.B.C.f vs ==> f xs
-- @
addDisplayForms :: QName -> TCM ()
addDisplayForms x = do
  reportSDoc "tc.display.section" 20 $ "Computing display forms for" <+> pretty x
  def <- getConstInfo x
  let v = case theDef def of
             Constructor{conSrcCon = h} -> Con h{ conName = x } ConOSystem []
             _                          -> Def x []

  -- Compute all unfoldings of x by repeatedly calling reduceDefCopy
  vs <- unfoldings x v
  reportSDoc "tc.display.section" 20 $ nest 2 $ vcat
    [ "unfoldings:" <?> vcat [ "-" <+> pretty v | v <- vs ] ]

  -- Turn unfoldings into display forms
  npars <- subtract (projectionArgs def) <$> getContextSize
  let dfs = map (displayForm npars v) vs
  reportSDoc "tc.display.section" 20 $ nest 2 $ vcat
    [ "displayForms:" <?> vcat [ "-" <+> (pretty y <+> "-->" <?> pretty df) | (y, df) <- dfs ] ]

  -- and add them
  mapM_ (uncurry addDisplayForm) dfs
  where

    -- To get display forms for projections we need to unSpine here.
    view :: Term -> ([Arg ArgName], Term)
    view = second unSpine . lamView

    -- Given an unfolding `top = λ xs → y es` generate a display form
    -- `y es ==> top xs`. The first `npars` variables in `xs` are module parameters
    -- and should not be pattern variables, but matched literally.
    displayForm :: Nat -> Term -> Term -> (QName, DisplayForm)
    displayForm npars top v =
      case view v of
        (xs, Def y es)   -> (y,)         $ mkDisplay xs es
        (xs, Con h i es) -> (conName h,) $ mkDisplay xs es
        _ -> __IMPOSSIBLE__
      where
        mkDisplay xs es = Display (n - npars) es $ DTerm $ top `apply` args
          -- Andreas, 2023-01-26, #6476:
          -- I think this @apply@ is safe (rather than @DTerm' top (map Apply args)@).
          where
            n    = length xs
            args = zipWith (\ x i -> var i <$ x) xs (downFrom n)

    -- Unfold a single defCopy.
    unfoldOnce :: Term -> TCM (Reduced () Term)
    unfoldOnce v = case view v of
      (xs, Def f es)   -> (fmap . fmap) (unlamView xs) (reduceDefCopyTCM f es)
      (xs, Con c i es) -> (fmap . fmap) (unlamView xs) (reduceDefCopyTCM (conName c) es)
      _                -> pure $ NoReduction ()

    -- Compute all reduceDefCopy unfoldings of `x`. Stop when we hit a non-copy.
    unfoldings :: QName -> Term -> TCM [Term]
    unfoldings x v = unfoldOnce v >>= \ case
      NoReduction{}     -> return []
      YesReduction _ v' -> do
        let headSymbol = case snd $ view v' of
              Def y _   -> Just y
              Con y _ _ -> Just (conName y)
              _         -> Nothing
        case headSymbol of
          Nothing -> return []
          Just y | x == y -> do
            -- This should never happen, but if it does, getting an __IMPOSSIBLE__ is much better
            -- than looping.
            reportSDoc "impossible" 10 $ nest 2 $ vcat
              [ "reduceDefCopy said YesReduction but the head symbol is the same!?"
              , nest 2 $ "v  =" <+> pretty v
              , nest 2 $ "v' =" <+> pretty v'
              ]
            __IMPOSSIBLE__
          Just y -> do
            ifM (defCopy <$> getConstInfo y)
                ((v' :) <$> unfoldings y v')  -- another copy so keep going
                (return [v'])                 -- not a copy, we stop

-- | Module application (followed by module parameter abstraction).
applySection
  :: ModuleName     -- ^ Name of new module defined by the module macro.
  -> Telescope      -- ^ Parameters of new module.
  -> ModuleName     -- ^ Name of old module applied to arguments.
  -> Args           -- ^ Arguments of module application.
  -> ScopeCopyInfo  -- ^ Imported names and modules
  -> TCM ()
applySection new ptel old ts ScopeCopyInfo{ renModules = rm, renNames = rd } = do
  rd <- closeConstructors rd
  applySection' new ptel old ts ScopeCopyInfo{ renModules = rm, renNames = rd }
  where
    -- If a datatype is being copied, all its constructors need to be copied,
    -- and if a constructor is copied its datatype needs to be.
    closeConstructors :: Ren QName -> TCM (Ren QName)
    closeConstructors rd = do
        ds <- nubOn id . catMaybes <$> traverse constructorData (Map.keys rd)
        cs <- nubOn id . concat    <$> traverse dataConstructors (Map.keys rd)
        new <- Map.unionsWith (<>) <$> traverse rename (ds ++ cs)
        reportSDoc "tc.mod.apply.complete" 30 $
          "also copying: " <+> pretty new
        return $ Map.unionWith (<>) new rd
      where
        rename :: QName -> TCM (Ren QName)
        rename x
          | x `Map.member` rd = pure mempty
          | otherwise =
              Map.singleton x . pure . qnameFromList . singleton <$> freshName_ (prettyShow $ qnameName x)

        constructorData :: QName -> TCM (Maybe QName)
        constructorData x = do
          (theDef <$> getConstInfo x) <&> \case
            Constructor{ conData = d } -> Just d
            _                          -> Nothing

        dataConstructors :: QName -> TCM [QName]
        dataConstructors x = do
          (theDef <$> getConstInfo x) <&> \case
            Datatype{ dataCons = cs } -> cs
            Record{ recConHead = h }  -> [conName h]
            _                         -> []

applySection' :: ModuleName -> Telescope -> ModuleName -> Args -> ScopeCopyInfo -> TCM ()
applySection' new ptel old ts ScopeCopyInfo{ renNames = rd, renModules = rm } = do
  do
    noCopyList <- catMaybes <$> mapM getName' constrainedPrims
    for_ (Map.keys rd) $ \ q ->
      when (q `elem` noCopyList) $ typeError (TriedToCopyConstrainedPrim q)

  reportSDoc "tc.mod.apply" 10 $ vcat
    [ "applySection"
    , "new  =" <+> pretty new
    , "ptel =" <+> pretty ptel
    , "old  =" <+> pretty old
    , "ts   =" <+> pretty ts
    ]
  _ <- Map.traverseWithKey (traverse . copyDef ts) rd
  _ <- Map.traverseWithKey (traverse . copySec ts) rm
  computePolarity (Map.elems rd >>= List1.toList)
  where
    -- Andreas, 2013-10-29
    -- Here, if the name x is not imported, it persists as
    -- old, possibly out-of-scope name.
    -- This old name may used by the case split tactic, leading to
    -- names that cannot be printed properly.
    -- I guess it would make sense to mark non-imported names
    -- as such (out-of-scope) and let splitting fail if it would
    -- produce out-of-scope constructors.
    --
    -- Taking 'List1.head' because 'Module.Data.cons' and 'Module.cons' are
    -- equivalent valid names and either can be used.
    copyName x = maybe x List1.head (Map.lookup x rd)

    argsToUse x = do
      let m = commonParentModule old x
      reportSDoc "tc.mod.apply" 80 $ "Common prefix: " <+> pretty m
      size <$> lookupSection m

    copyDef :: Args -> QName -> QName -> TCM ()
    copyDef ts x y = do
      def <- getConstInfo x
      np  <- argsToUse (qnameModule x)
      -- Issue #3083: We need to use the hiding from the telescope of the
      -- original module. This can be different than the hiding for the common
      -- parent in the case of record modules.
      hidings <- map getHiding . telToList <$> lookupSection (qnameModule x)
      let ts' = zipWith setHiding hidings ts
      commonTel <- lookupSection (commonParentModule old $ qnameModule x)
      reportSDoc "tc.mod.apply" 80 $ vcat
        [ "copyDef" <+> pretty x <+> "->" <+> pretty y
        , "ts' = " <+> pretty ts' ]
      -- The module telescope had been divided by some μ, so the corresponding
      -- top level definition had type μ \ Γ → B, so if we have a substitution
      -- Δ → Γ we actually want to apply μ \ - to it, so the new top-level
      -- definition we get will have signature μ \ Δ → B.  This is only valid
      -- for pure modality systems though.
      let ai = defArgInfo def
          m = unitModality { modCohesion = getCohesion ai }
      localTC (over eContext (map (mapModality (m `inverseComposeModality`)))) $
        copyDef' ts' np def
      where
        copyDef' ts np d = do
          reportSDoc "tc.mod.apply" 60 $ "making new def for" <+> pretty y <+> "from" <+> pretty x <+> "with" <+> text (show np) <+> "args" <+> text (show $ defAbstract d)
          reportSDoc "tc.mod.apply" 80 $ vcat
            [ "args = " <+> text (show ts')
            , "old type = " <+> pretty (defType d) ]
          reportSDoc "tc.mod.apply" 80 $
            "new type = " <+> pretty t
          addConstant y =<< nd y
          makeProjection y
          -- Issue1238: the copied def should be an 'instance' if the original
          -- def is one. Skip constructors since the original constructor will
          -- still work as an instance.
          -- Issue5583: Don't skip constructures, because the original constructor doesn't always
          -- work. For instance if it's only available in an anonymous module generated by
          -- `open import M args`.
          whenJust inst $ \ c -> addNamedInstance y c
          -- Set display form for the old name if it's not a constructor.
{- BREAKS fail/Issue478
          -- Andreas, 2012-10-20 and if we are not an anonymous module
          -- unless (isAnonymousModuleName new || isCon || not (null ptel)) $ do
-}
          -- BREAKS fail/Issue1643a
          -- -- Andreas, 2015-09-09 Issue 1643:
          -- -- Do not add a display form for a bare module alias.
          -- when (not isCon && null ptel && not (null ts)) $ do
          when (null ptel) $ do
            addDisplayForms y
          where
            ts' = take np ts
            t   = defType d `piApply` ts'
            pol = defPolarity d `apply` ts'
            occ = defArgOccurrences d `apply` ts'
            gen = defArgGeneralizable d `apply` ts'
            inst = defInstance d
            -- the name is set by the addConstant function
            nd :: QName -> TCM Definition
            nd y = do
              -- The arguments may use some feature of the current
              -- language.
              lang <- getLanguage
              for def $ \ df -> Defn
                    { defArgInfo        = defArgInfo d
                    , defName           = y
                    , defType           = t
                    , defSizedType      = defSizedType d
                    , defPolarity       = pol
                    , defArgOccurrences = occ
                    , defArgGeneralizable = gen
                    , defGeneralizedParams = [] -- This is only needed for type checking data/record defs so no need to copy it.
                    , defDisplay        = []
                    , defMutual         = -1   -- TODO: mutual block?
                    , defCompiledRep    = noCompiledRep
                    , defInstance       = inst
                    , defCopy           = True
                    , defMatchable      = Set.empty
                    , defNoCompilation  = defNoCompilation d
                    , defInjective      = False
                    , defCopatternLHS   = isCopatternLHS [cl]
                    , defBlocked        = defBlocked d
                    , defLanguage       =
                      case defLanguage d of
                        -- Note that Cubical Agda code can be imported
                        -- when --erased-cubical is used.
                        l@(Cubical CFull) -> l
                        Cubical CErased   -> lang
                        WithoutK          -> lang
                        WithK             -> lang
                    , theDef            = df }
            oldDef = theDef d
            isCon  = case oldDef of { Constructor{} -> True ; _ -> False }
            mutual = case oldDef of { Function{funMutual = m} -> m              ; _ -> Nothing }
            extlam = case oldDef of { Function{funExtLam = e} -> e              ; _ -> Nothing }
            with   = case oldDef of { Function{funWith = w}   -> copyName <$> w ; _ -> Nothing }
            -- Andreas, 2015-05-11, to fix issue 1413:
            -- Even if we apply the record argument (must be @var 0@), we stay a projection.
            -- This is because we may abstract the record argument later again.
            -- See succeed/ProjectionNotNormalized.agda
            isVar0 t = case unArg t of Var 0 [] -> True; _ -> False
            proj :: Either ProjectionLikenessMissing Projection
            proj   = case oldDef of
              Function{funProjection = Right p@Projection{projIndex = n}}
                | size ts' < n || (size ts' == n && maybe True isVar0 (lastMaybe ts'))
                -> Right p { projIndex = n - size ts'
                           , projLams  = projLams p `apply` ts'
                           , projProper= copyName <$> projProper p
                           }
              -- Preserve no-projection-likeness flag if it exists, and
              -- it's set to @Left _@. For future reference: The match
              -- on left can't be simplified or it accidentally
              -- circumvents the guard above.
              Function{funProjection = Left projl} -> Left projl
              _ -> Left MaybeProjection
            def =
              case oldDef of
                Constructor{ conPars = np, conData = d } -> return $
                  oldDef { conPars = np - size ts'
                         , conData = copyName d
                         }
                Datatype{ dataPars = np, dataCons = cs } -> return $
                  oldDef { dataPars   = np - size ts'
                         , dataClause = Just cl
                         , dataCons   = map copyName cs
                         }
                Record{ recPars = np, recTel = tel } -> return $
                  oldDef { recPars    = np - size ts'
                         , recClause  = Just cl
                         , recTel     = apply tel ts'
                         }
                GeneralizableVar -> return GeneralizableVar
                _ -> do
                  (mst, _, cc) <- compileClauses Nothing [cl] -- Andreas, 2012-10-07 non need for record pattern translation
                  fun          <- emptyFunctionData
                  let newDef =
                        set funMacro  (oldDef ^. funMacro) $
                        set funStatic (oldDef ^. funStatic) $
                        set funInline True $
                        FunctionDefn fun
                        { _funClauses        = [cl]
                        , _funCompiled       = Just cc
                        , _funSplitTree      = mst
                        , _funMutual         = mutual
                        , _funProjection     = proj
                        , _funTerminates     = Just True
                        , _funExtLam         = extlam
                        , _funWith           = with
                        }
                  reportSDoc "tc.mod.apply" 80 $ ("new def for" <+> pretty x) <?> pretty newDef
                  return newDef

            cl = Clause { clauseLHSRange    = getRange $ defClauses d
                        , clauseFullRange   = getRange $ defClauses d
                        , clauseTel         = EmptyTel
                        , namedClausePats   = []
                        , clauseBody        = Just $ dropArgs pars $ case oldDef of
                            Function{funProjection = Right p} -> projDropParsApply p ProjSystem rel ts'
                            _ -> Def x $ map Apply ts'
                        , clauseType        = Just $ defaultArg t
                        , clauseCatchall    = False
                        , clauseExact       = Just True
                        , clauseRecursive   = Just False -- definitely not recursive
                        , clauseUnreachable = Just False -- definitely not unreachable
                        , clauseEllipsis    = NoEllipsis
                        , clauseWhereModule = Nothing
                        }
              where
                -- The number of remaining parameters. We need to drop the
                -- lambdas corresponding to these from the clause body above.
                pars = max 0 $ either (const 0) (pred . projIndex) proj
                rel  = getRelevance $ defArgInfo d

    {- Example

    module Top Θ where
      module A Γ where
        module M Φ where
      module B Δ where
        module N Ψ where
          module O Ψ' where
        open A public     -- introduces only M --> A.M into the *scope*
    module C Ξ = Top.B ts

    new section C
      tel = Ξ.(Θ.Δ)[ts]

    calls
      1. copySec ts Top.A.M C.M
      2. copySec ts Top.B.N C.N
      3. copySec ts Top.B.N.O C.N.O
    with
      old = Top.B

    For 1.
      Common prefix is: Top
      totalArgs = |Θ|   (section Top)
      tel       = Θ.Γ.Φ (section Top.A.M)
      ts'       = take totalArgs ts
      Θ₂        = drop totalArgs Θ
      new section C.M
        tel =  Θ₂.Γ.Φ[ts']
    -}
    copySec :: Args -> ModuleName -> ModuleName -> TCM ()
    copySec ts x y = do
      totalArgs <- argsToUse x
      tel       <- lookupSection x
      let sectionTel =  apply tel $ take totalArgs ts
      reportSDoc "tc.mod.apply" 80 $ "Copying section" <+> pretty x <+> "to" <+> pretty y
      reportSDoc "tc.mod.apply" 80 $ "  ts           = " <+> mconcat (List.intersperse "; " (map pretty ts))
      reportSDoc "tc.mod.apply" 80 $ "  totalArgs    = " <+> text (show totalArgs)
      reportSDoc "tc.mod.apply" 80 $ "  tel          = " <+> text (unwords (map (fst . unDom) $ telToList tel))  -- only names
      reportSDoc "tc.mod.apply" 80 $ "  sectionTel   = " <+> text (unwords (map (fst . unDom) $ telToList ptel)) -- only names
      addContext sectionTel $ addSection y

-- | Add a display form to a definition (could be in this or imported signature).
addDisplayForm :: QName -> DisplayForm -> TCM ()
addDisplayForm x df = do
  d <- makeOpen df
  let add = updateDefinition x $ \ def -> def{ defDisplay = d : defDisplay def }
  ifM (isLocal x)
    {-then-} (modifySignature add)
    {-else-} (stImportsDisplayForms `modifyTCLens` HMap.insertWith (++) x [d])
  whenM (hasLoopingDisplayForm x) $
    typeError . GenericDocError =<< do "Cannot add recursive display form for" <+> pretty x

isLocal :: ReadTCState m => QName -> m Bool
isLocal x = HMap.member x <$> useR (stSignature . sigDefinitions)

getDisplayForms :: (HasConstInfo m, ReadTCState m) => QName -> m [LocalDisplayForm]
getDisplayForms q = do
  ds  <- either (const []) defDisplay <$> getConstInfo' q
  ds1 <- HMap.lookupDefault [] q <$> useR stImportsDisplayForms
  ds2 <- HMap.lookupDefault [] q <$> useR stImportedDisplayForms
  ifM (isLocal q) (return $ ds ++ ds1 ++ ds2)
                  (return $ ds1 ++ ds ++ ds2)

hasDisplayForms :: (HasConstInfo m, ReadTCState m) => QName -> m Bool
hasDisplayForms = fmap (not . null) . getDisplayForms

-- | Find all names used (recursively) by display forms of a given name.
chaseDisplayForms :: QName -> TCM (Set QName)
chaseDisplayForms q = go Set.empty [q]
  where
    go :: Set QName        -- Accumulator.
       -> [QName]          -- Work list.  TODO: make work set to avoid duplicate chasing?
       -> TCM (Set QName)
    go used []       = pure used
    go used (q : qs) = do
      let rhs (Display _ _ e) = e   -- Only look at names in the right-hand side (#1870)
      let notYetUsed x = if x `Set.member` used then Set.empty else Set.singleton x
      ds <- namesIn' notYetUsed . map (rhs . dget)
            <$> (getDisplayForms q `catchError_` \ _ -> pure [])  -- might be a pattern synonym
      go (Set.union ds used) (Set.toList ds ++ qs)

-- | Check if a display form is looping.
hasLoopingDisplayForm :: QName -> TCM Bool
hasLoopingDisplayForm q = Set.member q <$> chaseDisplayForms q

canonicalName :: HasConstInfo m => QName -> m QName
canonicalName x = do
  def <- theDef <$> getConstInfo x
  case def of
    Constructor{conSrcCon = c}                                -> return $ conName c
    Record{recClause = Just (Clause{ clauseBody = body })}    -> can body
    Datatype{dataClause = Just (Clause{ clauseBody = body })} -> can body
    _                                                         -> return x
  where
    can body = canonicalName $ extract $ fromMaybe __IMPOSSIBLE__ body
    extract (Def x _)  = x
    extract _          = __IMPOSSIBLE__

sameDef :: HasConstInfo m => QName -> QName -> m (Maybe QName)
sameDef d1 d2 = do
  c1 <- canonicalName d1
  c2 <- canonicalName d2
  if (c1 == c2) then return $ Just c1 else return Nothing

-- | Does the given constructor come from a single-constructor type?
--
-- Precondition: The name has to refer to a constructor.
singleConstructorType :: QName -> TCM Bool
singleConstructorType q = do
  d <- theDef <$> getConstInfo q
  case d of
    Record {}                   -> return True
    Constructor { conData = d } -> do
      di <- theDef <$> getConstInfo d
      return $ case di of
        Record {}                  -> True
        Datatype { dataCons = cs } -> natSize cs == 1
        _                          -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

-- | Signature lookup errors.
data SigError
  = SigUnknown String -- ^ The name is not in the signature; default error message.
  | SigAbstract       -- ^ The name is not available, since it is abstract.
  | SigCubicalNotErasure
    -- ^ The name is not available because it was defined in Cubical
    -- Agda, but the current language is Erased Cubical Agda, and
    -- @--erasure@ is not active.

-- | Generates an error message corresponding to
-- 'SigCubicalNotErasure' for a given 'QName'.
notSoPrettySigCubicalNotErasure :: QName -> String
notSoPrettySigCubicalNotErasure q =
  "The name " ++ prettyShow q ++ " which was defined in Cubical " ++
  "Agda can only be used in Erased Cubical Agda if the option " ++
  "--erasure is used"

-- | Generates an error message corresponding to
-- 'SigCubicalNotErasure' for a given 'QName'.
prettySigCubicalNotErasure :: MonadPretty m => QName -> m Doc
prettySigCubicalNotErasure q = fsep $
  pwords "The name" ++
  [prettyTCM q] ++
  pwords "which was defined in Cubical Agda can only be used in" ++
  pwords "Erased Cubical Agda if the option --erasure is used"

-- | An eliminator for 'SigError'. All constructors except for
-- 'SigAbstract' are assumed to be impossible.
sigError :: (HasCallStack, MonadDebug m) => m a -> SigError -> m a
sigError a = \case
  SigUnknown s         -> __IMPOSSIBLE_VERBOSE__ s
  SigAbstract          -> a
  SigCubicalNotErasure -> __IMPOSSIBLE__

class ( Functor m
      , Applicative m
      , Fail.MonadFail m
      , HasOptions m
      , MonadDebug m
      , MonadTCEnv m
      ) => HasConstInfo m where
  -- | Lookup the definition of a name. The result is a closed thing, all free
  --   variables have been abstracted over.
  getConstInfo :: QName -> m Definition
  getConstInfo q = getConstInfo' q >>= \case
      Right d -> return d
      Left (SigUnknown err) -> __IMPOSSIBLE_VERBOSE__ err
      Left SigAbstract      -> __IMPOSSIBLE_VERBOSE__ $
        "Abstract, thus, not in scope: " ++ prettyShow q
      Left SigCubicalNotErasure -> __IMPOSSIBLE_VERBOSE__ $
        notSoPrettySigCubicalNotErasure q

  -- | Version that reports exceptions:
  getConstInfo' :: QName -> m (Either SigError Definition)
  -- getConstInfo' q = Right <$> getConstInfo q -- conflicts with default signature

  -- | Lookup the rewrite rules with the given head symbol.
  getRewriteRulesFor :: QName -> m RewriteRules

  -- Lifting HasConstInfo through monad transformers:

  default getConstInfo'
    :: (HasConstInfo n, MonadTrans t, m ~ t n)
    => QName -> m (Either SigError Definition)
  getConstInfo' = lift . getConstInfo'

  default getRewriteRulesFor
    :: (HasConstInfo n, MonadTrans t, m ~ t n)
    => QName -> m RewriteRules
  getRewriteRulesFor = lift . getRewriteRulesFor

{-# SPECIALIZE getConstInfo :: QName -> TCM Definition #-}

{-# SPECIALIZE getOriginalConstInfo :: QName -> TCM Definition #-}
-- | The computation 'getConstInfo' sometimes tweaks the returned
-- 'Definition', depending on the current 'Language' and the
-- 'Language' of the 'Definition'. This variant of 'getConstInfo' does
-- not perform any tweaks.
getOriginalConstInfo ::
  (ReadTCState m, HasConstInfo m) => QName -> m Definition
getOriginalConstInfo q = do
  def  <- getConstInfo q
  lang <- getLanguage
  case (lang, defLanguage def) of
    (Cubical CErased, Cubical CFull) ->
      locallyTCState
        (stPragmaOptions . lensOptCubical)
        (const $ Just CFull)
        (getConstInfo q)
    _ -> return def

defaultGetRewriteRulesFor :: (ReadTCState m, MonadTCEnv m) => QName -> m RewriteRules
defaultGetRewriteRulesFor q = ifNotM (shouldReduceDef q) (return []) $ do
  st <- getTCState
  let sig = st ^. stSignature
      imp = st ^. stImports
      look s = HMap.lookup q $ s ^. sigRewriteRules
  return $ mconcat $ catMaybes [look sig, look imp]

-- | Get the original name of the projection
--   (the current one could be from a module application).
getOriginalProjection :: HasConstInfo m => QName -> m QName
getOriginalProjection q = projOrig . fromMaybe __IMPOSSIBLE__ <$> isProjection q

instance HasConstInfo (TCMT IO) where
  getRewriteRulesFor = defaultGetRewriteRulesFor
  getConstInfo' q = do
    st  <- getTC
    env <- askTC
    defaultGetConstInfo st env q
  getConstInfo q = getConstInfo' q >>= \case
      Right d -> return d
      Left (SigUnknown err)     -> fail err
      Left SigAbstract          -> notInScopeError $ qnameToConcrete q
      Left SigCubicalNotErasure ->
        typeError . GenericDocError =<< prettySigCubicalNotErasure q

defaultGetConstInfo
  :: (HasOptions m, MonadDebug m, MonadTCEnv m)
  => TCState -> TCEnv -> QName -> m (Either SigError Definition)
defaultGetConstInfo st env q = do
    let defs  = st ^. stSignature . sigDefinitions
        idefs = st ^. stImports   . sigDefinitions
    case catMaybes [HMap.lookup q defs, HMap.lookup q idefs] of
        []  -> return $ Left $ SigUnknown $ "Unbound name: " ++ prettyShow q ++ showQNameId q
        [d] -> checkErasureFixQuantity d >>= \case
                 Left err -> return (Left err)
                 Right d  -> mkAbs env d
        ds  -> __IMPOSSIBLE_VERBOSE__ $ "Ambiguous name: " ++ prettyShow q
    where
      mkAbs env d
        -- Apply the reducibility rules (abstract, opaque) to check
        -- whether the definition should be hidden behind an
        -- 'AbstractDef'.
        | not (isAccessibleDef env st d{defName = q'}) =
          case alwaysMakeAbstract d of
            Just d      -> return $ Right d
            Nothing     -> return $ Left SigAbstract
              -- the above can happen since the scope checker is a bit sloppy with 'abstract'
        | otherwise = return $ Right d
        where
          q' = case theDef d of
            -- Hack to make abstract constructors work properly. The constructors
            -- live in a module with the same name as the datatype, but for 'abstract'
            -- purposes they're considered to be in the same module as the datatype.
            Constructor{} -> dropLastModule q
            _             -> q

          dropLastModule q@QName{ qnameModule = m } =
            q{ qnameModule = mnameFromList $
                 initWithDefault __IMPOSSIBLE__ $ mnameToList m
             }

      -- Names defined in Cubical Agda may only be used in Erased
      -- Cubical Agda if --erasure is used. In that case they are (to
      -- a large degree) treated as erased.
      checkErasureFixQuantity d = do
        current <- getLanguage
        if defLanguage d == Cubical CFull &&
           current == Cubical CErased
        then do
          erasure <- optErasure <$> pragmaOptions
          return $
            if erasure
            then Right $ setQuantity zeroQuantity d
            else Left SigCubicalNotErasure
        else return $ Right d

-- HasConstInfo lifts through monad transformers
-- (see default signatures in HasConstInfo class).

instance HasConstInfo m => HasConstInfo (ChangeT m)
instance HasConstInfo m => HasConstInfo (ExceptT err m)
instance HasConstInfo m => HasConstInfo (IdentityT m)
instance HasConstInfo m => HasConstInfo (ListT m)
instance HasConstInfo m => HasConstInfo (MaybeT m)
instance HasConstInfo m => HasConstInfo (ReaderT r m)
instance HasConstInfo m => HasConstInfo (StateT s m)
instance (Monoid w, HasConstInfo m) => HasConstInfo (WriterT w m)
instance HasConstInfo m => HasConstInfo (BlockT m)

{-# INLINE getConInfo #-}
getConInfo :: HasConstInfo m => ConHead -> m Definition
getConInfo = getConstInfo . conName

-- | Look up the polarity of a definition.
getPolarity :: HasConstInfo m => QName -> m [Polarity]
getPolarity q = defPolarity <$> getConstInfo q

-- | Look up polarity of a definition and compose with polarity
--   represented by 'Comparison'.
getPolarity' :: HasConstInfo m => Comparison -> QName -> m [Polarity]
getPolarity' CmpEq  q = map (composePol Invariant) <$> getPolarity q -- return []
getPolarity' CmpLeq q = getPolarity q -- composition with Covariant is identity

-- | Set the polarity of a definition.
setPolarity :: (MonadTCState m, MonadDebug m) => QName -> [Polarity] -> m ()
setPolarity q pol = do
  reportSDoc "tc.polarity.set" 20 $
    "Setting polarity of" <+> pretty q <+> "to" <+> pretty pol <> "."
  modifySignature $ updateDefinition q $ updateDefPolarity $ const pol

-- | Look up the forced arguments of a definition.
getForcedArgs :: HasConstInfo m => QName -> m [IsForced]
getForcedArgs q = defForced <$> getConstInfo q

-- | Get argument occurrence info for argument @i@ of definition @d@ (never fails).
getArgOccurrence :: QName -> Nat -> TCM Occurrence
getArgOccurrence d i = do
  def <- getConstInfo d
  return $! case theDef def of
    Constructor{} -> StrictPos
    _             -> fromMaybe Mixed $ defArgOccurrences def !!! i

-- | Sets the 'defArgOccurrences' for the given identifier (which
-- should already exist in the signature).
setArgOccurrences :: MonadTCState m => QName -> [Occurrence] -> m ()
setArgOccurrences d os = modifyArgOccurrences d $ const os

modifyArgOccurrences :: MonadTCState m => QName -> ([Occurrence] -> [Occurrence]) -> m ()
modifyArgOccurrences d f =
  modifySignature $ updateDefinition d $ updateDefArgOccurrences f

setTreeless :: QName -> TTerm -> TCM ()
setTreeless q t =
  modifyGlobalDefinition q $ updateTheDef $ \case
    fun@Function{} -> fun{ funTreeless = Just $ Compiled t Nothing }
    _ -> __IMPOSSIBLE__

setCompiledArgUse :: QName -> [ArgUsage] -> TCM ()
setCompiledArgUse q use =
  modifyGlobalDefinition q $ updateTheDef $ \case
    fun@Function{} ->
      fun{ funTreeless = funTreeless fun <&> \ c -> c { cArgUsage = Just use } }
    _ -> __IMPOSSIBLE__

getCompiled :: HasConstInfo m => QName -> m (Maybe Compiled)
getCompiled q = do
  (theDef <$> getConstInfo q) <&> \case
    Function{ funTreeless = t } -> t
    _                           -> Nothing

-- | Returns a list of length 'conArity'.
--   If no erasure analysis has been performed yet, this will be a list of 'False's.
getErasedConArgs :: HasConstInfo m => QName -> m [Bool]
getErasedConArgs q = do
  def <- getConstInfo q
  case theDef def of
    Constructor{ conArity, conErased } -> return $
      fromMaybe (replicate conArity False) conErased
    _ -> __IMPOSSIBLE__

setErasedConArgs :: QName -> [Bool] -> TCM ()
setErasedConArgs q args = modifyGlobalDefinition q $ updateTheDef $ \case
    def@Constructor{ conArity }
      | length args == conArity -> def{ conErased = Just args }
      | otherwise               -> __IMPOSSIBLE__
    def -> def   -- no-op for non-constructors

getTreeless :: HasConstInfo m => QName -> m (Maybe TTerm)
getTreeless q = fmap cTreeless <$> getCompiled q

getCompiledArgUse :: HasConstInfo m => QName -> m (Maybe [ArgUsage])
getCompiledArgUse q = (cArgUsage =<<) <$> getCompiled q

-- | add data constructors to a datatype
addDataCons :: QName -> [QName] -> TCM ()
addDataCons d cs = modifySignature $ updateDefinition d $ updateTheDef $ \ def ->
  let !cs' = cs ++ dataCons def in
  case def of
    Datatype{} -> def {dataCons = cs' }
    _          -> __IMPOSSIBLE__

-- | Get the mutually recursive identifiers of a symbol from the signature.
getMutual :: QName -> TCM (Maybe [QName])
getMutual d = getMutual_ . theDef <$> getConstInfo d

-- | Get the mutually recursive identifiers from a `Definition`.
getMutual_ :: Defn -> Maybe [QName]
getMutual_ = \case
    Function {  funMutual = m } -> m
    Datatype { dataMutual = m } -> m
    Record   {  recMutual = m } -> m
    _ -> Nothing

-- | Set the mutually recursive identifiers.
setMutual :: QName -> [QName] -> TCM ()
setMutual d m = modifySignature $ updateDefinition d $ updateTheDef $ \ def ->
  case def of
    Function{} -> def { funMutual = Just m }
    Datatype{} -> def {dataMutual = Just m }
    Record{}   -> def { recMutual = Just m }
    _          -> if null m then def else __IMPOSSIBLE__ -- nothing to do

-- | Check whether two definitions are mutually recursive.
mutuallyRecursive :: QName -> QName -> TCM Bool
mutuallyRecursive d d1 = (d `elem`) . fromMaybe __IMPOSSIBLE__ <$> getMutual d1

-- | A function/data/record definition is nonRecursive if it is not even mutually
--   recursive with itself.
definitelyNonRecursive_ :: Defn -> Bool
definitelyNonRecursive_ = maybe False null . getMutual_

-- | Get the number of parameters to the current module.
getCurrentModuleFreeVars :: TCM Nat
getCurrentModuleFreeVars = size <$> (lookupSection =<< currentModule)

--   For annoying reasons the qnameModule of a pattern lambda is not correct
--   (#2883), so make sure to grab the right module for those.
getDefModule :: HasConstInfo m => QName -> m (Either SigError ModuleName)
getDefModule f = mapRight modName <$> getConstInfo' f
  where
    modName def = case theDef def of
      Function{ funExtLam = Just (ExtLamInfo m _ _) } -> m
      _                                               -> qnameModule f

-- | Compute the number of free variables of a defined name. This is the sum of
--   number of parameters shared with the current module and the number of
--   anonymous variables (if the name comes from a let-bound module).
getDefFreeVars :: (Functor m, Applicative m, ReadTCState m, MonadTCEnv m) => QName -> m Nat
getDefFreeVars = getModuleFreeVars . qnameModule

freeVarsToApply :: (Functor m, HasConstInfo m, HasOptions m,
                    ReadTCState m, MonadTCEnv m, MonadDebug m)
                => QName -> m Args
freeVarsToApply q = do
  vs <- moduleParamsToApply $ qnameModule q
  -- Andreas, 2021-07-14, issue #5470
  -- getConstInfo will fail if q is not in scope,
  -- but in this case there are no free vars to apply, since
  -- we cannot be in a child module of its defining module.
  -- So if we short cut the nil-case here, we avoid the internal error of #5470.
  if null vs then return [] else do
  t <- defType <$> getConstInfo q
  let TelV tel _ = telView'UpTo (size vs) t
  unless (size tel == size vs) __IMPOSSIBLE__
  return $ zipWith (\ arg dom -> unArg arg <$ argFromDom dom) vs $ telToList tel

{-# SPECIALIZE getModuleFreeVars :: ModuleName -> TCM Nat #-}
{-# SPECIALIZE getModuleFreeVars :: ModuleName -> ReduceM Nat #-}
getModuleFreeVars :: (Functor m, Applicative m, MonadTCEnv m, ReadTCState m)
                  => ModuleName -> m Nat
getModuleFreeVars m = do
  m0   <- commonParentModule m <$> currentModule
  (+) <$> getAnonymousVariables m <*> (size <$> lookupSection m0)

-- | Compute the context variables to apply a definition to.
--
--   We have to insert the module telescope of the common prefix
--   of the current module and the module where the definition comes from.
--   (Properly raised to the current context.)
--
--   Example:
--   @
--      module M₁ Γ where
--        module M₁ Δ where
--          f = ...
--        module M₃ Θ where
--          ... M₁.M₂.f [insert Γ raised by Θ]
--   @
moduleParamsToApply :: (Functor m, Applicative m, HasOptions m,
                        MonadTCEnv m, ReadTCState m, MonadDebug m)
                    => ModuleName -> m Args
moduleParamsToApply m = do

  traceSDoc "tc.sig.param" 90 ("computing module parameters of " <+> pretty m) $ do

  -- Jesper, 2020-01-22: If the module parameter substitution for the
  -- module cannot be found, that likely means we are within a call to
  -- @inTopContext@. In that case we should provide no arguments for
  -- the module parameters (see #4383).
  caseMaybeM (getModuleParameterSub m) (return []) $ \sub -> do

  traceSDoc "tc.sig.param" 60 (do
    cxt <- getContext
    nest 2 $ vcat
      [ "cxt  = " <+> prettyTCM (PrettyContext cxt)
      , "sub  = " <+> pretty sub
      ]) $ do

  -- Get the correct number of free variables (correctly raised) of @m@.
  n   <- getModuleFreeVars m
  traceSDoc "tc.sig.param" 60 (nest 2 $ "n    = " <+> text (show n)) $ do
  tel <- take n . telToList <$> lookupSection m
  traceSDoc "tc.sig.param" 60 (nest 2 $ "tel  = " <+> pretty tel) $ do
  unless (size tel == n) __IMPOSSIBLE__
  let args = applySubst sub $ zipWith (\ i a -> var i <$ argFromDom a) (downFrom n) tel
  traceSDoc "tc.sig.param" 60 (nest 2 $ "args = " <+> prettyList_ (map pretty args)) $ do

  -- Apply the original ArgInfo, as the hiding information in the current
  -- context might be different from the hiding information expected by @m@.

  getSection m >>= \case
    Nothing -> do
      -- We have no section for @m@.
      -- This should only happen for toplevel definitions, and then there
      -- are no free vars to apply, or?
      -- unless (null args) __IMPOSSIBLE__
      -- No, this invariant is violated by private modules, see Issue1701a.
      return args
    Just (Section stel) -> do
      -- The section telescope of @m@ should be as least
      -- as long as the number of free vars @m@ is applied to.
      -- We still check here as in no case, we want @zipWith@ to silently
      -- drop some @args@.
      -- And there are also anonymous modules, thus, the invariant is not trivial.
      when (size stel < size args) __IMPOSSIBLE__
      return $ zipWith (\ !dom (Arg _ v) -> v <$ argFromDom dom) (telToList stel) args

-- | Unless all variables in the context are module parameters, create a fresh
--   module to capture the non-module parameters. Used when unquoting to make
--   sure generated definitions work properly.
inFreshModuleIfFreeParams :: TCM a -> TCM a
inFreshModuleIfFreeParams k = do
  msub <- getModuleParameterSub =<< currentModule
  if isNothing msub || msub == Just IdS then k else do
    m  <- currentModule
    m' <- qualifyM m . mnameFromList1 . singleton <$>
            freshName_ ("_" :: String)
    addSection m'
    withCurrentModule m' k

-- | Instantiate a closed definition with the correct part of the current
--   context.
{-# SPECIALIZE instantiateDef :: Definition -> TCM Definition #-}
instantiateDef
  :: ( Functor m, HasConstInfo m, HasOptions m
     , ReadTCState m, MonadTCEnv m, MonadDebug m )
  => Definition -> m Definition
instantiateDef d = do
  vs  <- freeVarsToApply $ defName d
  verboseS "tc.sig.inst" 30 $ do
    ctx <- getContext
    m   <- currentModule
    reportSDoc "tc.sig.inst" 30 $
      "instDef in" <+> pretty m <> ":" <+> pretty (defName d) <+>
      fsep (map pretty $ zipWith (<$) (reverse $ map (fst . unDom) ctx) vs)
  return $ d `apply` vs

instantiateRewriteRule :: (Functor m, HasConstInfo m, HasOptions m,
                           ReadTCState m, MonadTCEnv m, MonadDebug m)
                       => RewriteRule -> m RewriteRule
instantiateRewriteRule rew = do
  traceSDoc "rewriting" 95 ("instantiating rewrite rule" <+> pretty (rewName rew) <+> "to the local context.") $ do
  vs  <- freeVarsToApply $ rewName rew
  let rew' = rew `apply` vs
  traceSLn "rewriting" 95 ("instantiated rewrite rule: ") $ do
  traceSLn "rewriting" 95 (show rew') $ do
  return rew'

instantiateRewriteRules :: (Functor m, HasConstInfo m, HasOptions m,
                            ReadTCState m, MonadTCEnv m, MonadDebug m)
                        => RewriteRules -> m RewriteRules
instantiateRewriteRules = mapM instantiateRewriteRule

-- | Return the abstract view of a definition, /regardless/ of whether
-- the definition would be treated abstractly.
alwaysMakeAbstract :: Definition -> Maybe Definition
alwaysMakeAbstract d =
  do
    def <- makeAbs $ theDef d
    pure d { defArgOccurrences = [] -- no positivity info for abstract things!
           , defPolarity       = [] -- no polarity info for abstract things!
           , theDef = def
           }
  where
    makeAbs d@Axiom{}            = Just d
    makeAbs d@DataOrRecSig{}     = Just d
    makeAbs d@GeneralizableVar{} = Just d
    makeAbs d@Datatype {} = Just $ AbstractDefn d
    makeAbs d@Function {} = Just $ AbstractDefn d
    makeAbs Constructor{} = Nothing
    -- Andreas, 2012-11-18:  Make record constructor and projections abstract.
    -- Andreas, 2017-08-14:  Projections are actually not abstract (issue #2682).
    -- Return the Defn under a wrapper to allow e.g. eligibleForProjectionLike
    -- to see whether the abstract thing is a record type or not.
    makeAbs d@Record{}    = Just $ AbstractDefn d
    makeAbs Primitive{}   = __IMPOSSIBLE__
    makeAbs PrimitiveSort{} = __IMPOSSIBLE__
    makeAbs AbstractDefn{} = __IMPOSSIBLE__

-- | Enter abstract mode. Abstract definition in the current module are transparent.
{-# SPECIALIZE inAbstractMode :: TCM a -> TCM a #-}
inAbstractMode :: MonadTCEnv m => m a -> m a
inAbstractMode = localTC $ \e -> e { envAbstractMode = AbstractMode }

-- | Not in abstract mode. All abstract definitions are opaque.
{-# SPECIALIZE inConcreteMode :: TCM a -> TCM a #-}
inConcreteMode :: MonadTCEnv m => m a -> m a
inConcreteMode = localTC $ \e -> e { envAbstractMode = ConcreteMode }

-- | Ignore abstract mode. All abstract definitions are transparent.
ignoreAbstractMode :: MonadTCEnv m => m a -> m a
ignoreAbstractMode = localTC $ \e -> e { envAbstractMode = IgnoreAbstractMode }

-- | Go under the given opaque block. The unfolding set will turn opaque
-- definitions transparent.
{-# SPECIALIZE underOpaqueId :: OpaqueId -> TCM a -> TCM a #-}
underOpaqueId :: MonadTCEnv m => OpaqueId -> m a -> m a
underOpaqueId i = localTC $ \e -> e { envCurrentOpaqueId = Just i }

-- | Outside of any opaque blocks.
{-# SPECIALIZE notUnderOpaque :: TCM a -> TCM a #-}
notUnderOpaque :: MonadTCEnv m => m a -> m a
notUnderOpaque = localTC $ \e -> e { envCurrentOpaqueId = Nothing }

-- | Enter the reducibility environment associated with a definition:
-- The environment will have the same concreteness as the name, and we
-- will be in the opaque block enclosing the name, if any.
{-# SPECIALIZE inConcreteOrAbstractMode :: QName -> (Definition -> TCM a) -> TCM a #-}
inConcreteOrAbstractMode :: (MonadTCEnv m, HasConstInfo m) => QName -> (Definition -> m a) -> m a
inConcreteOrAbstractMode q cont = do
  -- Andreas, 2015-07-01: If we do not ignoreAbstractMode here,
  -- we will get ConcreteDef for abstract things, as they are turned into axioms.
  def <- ignoreAbstractMode $ getConstInfo q
  let
    k1 = case defAbstract def of
      AbstractDef -> inAbstractMode
      ConcreteDef -> inConcreteMode

    k2 = case defOpaque def of
      OpaqueDef i    -> underOpaqueId i
      TransparentDef -> notUnderOpaque
  k2 (k1 (cont def))

-- | Get type of a constant, instantiated to the current context.
{-# SPECIALIZE typeOfConst :: QName -> TCM Type #-}
typeOfConst :: (HasConstInfo m, ReadTCState m) => QName -> m Type
typeOfConst q = defType <$> (instantiateDef =<< getConstInfo q)

-- | Get relevance of a constant.
{-# SPECIALIZE relOfConst :: QName -> TCM Relevance #-}
relOfConst :: HasConstInfo m => QName -> m Relevance
relOfConst q = getRelevance <$> getConstInfo q

-- | Get modality of a constant.
{-# SPECIALIZE modalityOfConst :: QName -> TCM Modality #-}
modalityOfConst :: HasConstInfo m => QName -> m Modality
modalityOfConst q = getModality <$> getConstInfo q

-- | The number of dropped parameters for a definition.
--   0 except for projection(-like) functions and constructors.
droppedPars :: Definition -> Int
droppedPars d = case theDef d of
    Axiom{}                  -> 0
    DataOrRecSig{}           -> 0
    GeneralizableVar{}       -> 0
    def@Function{}           -> projectionArgs d
    Datatype  {dataPars = _} -> 0  -- not dropped
    Record     {recPars = _} -> 0  -- not dropped
    Constructor{conPars = n} -> n
    Primitive{}              -> 0
    PrimitiveSort{}          -> 0
    AbstractDefn{}           -> __IMPOSSIBLE__

-- | Is it the name of a record projection?
{-# SPECIALIZE isProjection :: QName -> TCM (Maybe Projection) #-}
isProjection :: HasConstInfo m => QName -> m (Maybe Projection)
isProjection qn = isProjection_ . theDef <$> getConstInfo qn

isProjection_ :: Defn -> Maybe Projection
isProjection_ def =
  case def of
    Function { funProjection = Right result } -> Just result
    _                                         -> Nothing

-- | Is it the name of a non-irrelevant record projection?
{-# SPECIALIZE isProjection :: QName -> TCM (Maybe Projection) #-}
isRelevantProjection :: HasConstInfo m => QName -> m (Maybe Projection)
isRelevantProjection qn = isRelevantProjection_ <$> getConstInfo qn

isRelevantProjection_ :: Definition -> Maybe Projection
isRelevantProjection_ def =
  if isIrrelevant def then Nothing else isProjection_ $ theDef def

-- | Is it a function marked STATIC?
isStaticFun :: Defn -> Bool
isStaticFun = (^. funStatic)

-- | Is it a function marked INLINE?
isInlineFun :: Defn -> Bool
isInlineFun = (^. funInline)

-- | Returns @True@ if we are dealing with a proper projection,
--   i.e., not a projection-like function nor a record field value
--   (projection applied to argument).
isProperProjection :: Defn -> Bool
isProperProjection d = caseMaybe (isProjection_ d) False $ \ isP ->
  (projIndex isP > 0) && isJust (projProper isP)

-- | Number of dropped initial arguments of a projection(-like) function.
projectionArgs :: Definition -> Int
projectionArgs = maybe 0 (max 0 . pred . projIndex) . isRelevantProjection_

-- | Check whether a definition uses copatterns.
usesCopatterns :: (HasConstInfo m) => QName -> m Bool
usesCopatterns q = defCopatternLHS <$> getConstInfo q

-- | Apply a function @f@ to its first argument, producing the proper
--   postfix projection if @f@ is a projection which is not irrelevant.
applyDef :: (HasConstInfo m)
         => ProjOrigin -> QName -> Arg Term -> m Term
applyDef o f a = do
  let fallback = return $ Def f [Apply a]
  -- Andreas, 2022-03-07, issue #5809: don't drop parameters of irrelevant projections.
  caseMaybeM (isRelevantProjection f) fallback $ \ isP -> do
    if projIndex isP <= 0 then fallback else do
      -- Get the original projection, if existing.
      if isNothing (projProper isP) then fallback else do
        return $ unArg a `applyE` [Proj o $ projOrig isP]
