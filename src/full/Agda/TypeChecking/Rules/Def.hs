{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Def where

import Prelude hiding ( null )

import Control.Monad        ( forM, forM_ )
import Control.Monad.Except ( MonadError(..) )

import Data.Bifunctor
import Data.Function (on)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup ( sconcat )

import Agda.Interaction.Options

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Pretty as C
import Agda.Syntax.Position
import Agda.Syntax.Abstract.Pattern as A
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern as I
import Agda.Syntax.Internal.MetaVars (allMetasList)
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Info hiding (defAbstract)

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Warnings ( warning )

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Inlining
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Patterns.Abstract (expandPatternSynonyms)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.With
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Telescope.Path
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.SizedTypes.Solve
import Agda.TypeChecking.Rewriting.Confluence
import Agda.TypeChecking.CompiledClause (CompiledClauses'(..), hasProjectionPatterns)
import Agda.TypeChecking.CompiledClause.Compile
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.RecordPatterns ( recordRHSToCopatterns )
import Agda.TypeChecking.Sort

import Agda.TypeChecking.Rules.Term
import Agda.TypeChecking.Rules.LHS                 ( checkLeftHandSide, LHSResult(..), bindAsPatterns )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl ( checkDecls )

import Agda.Utils.Function ( applyWhen )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1 ( List1, pattern (:|), (<|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Syntax.Common.Pretty ( prettyShow )
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Utils.Singleton
import Agda.Utils.Size
import qualified Agda.Utils.SmallSet as SmallSet
import Agda.Utils.Update

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Definitions by pattern matching
---------------------------------------------------------------------------

checkFunDef :: A.DefInfo -> QName -> [A.Clause] -> TCM ()
checkFunDef i name cs = do
        -- Reset blocking tag (in case a previous attempt was blocked)
        modifySignature $ updateDefinition name $ updateDefBlocked $ const $
          NotBlocked (MissingClauses name) ()
        -- Get the type and relevance of the function
        def <- instantiateDef =<< getConstInfo name
        let t    = defType def
        let info = getArgInfo def

        -- If the function is erased, then hard compile-time mode is
        -- entered.
        setHardCompileTimeModeIfErased' info $ do

        case isAlias cs t of  -- #418: Don't use checkAlias for abstract definitions, since the type
                              -- of an abstract function must not be informed by its definition.
          Just (e, mc, x)
            | Info.defAbstract i == ConcreteDef, Info.defOpaque i == TransparentDef ->
              traceCall (CheckFunDefCall (getRange i) name cs True) $ do
                -- Andreas, 2012-11-22: if the alias is in an abstract block
                -- it has been frozen.  We unfreeze it to enable type inference.
                -- See issue 729.
                -- Ulf, 2021-02-09: also unfreeze metas in the sort of this type
                whenM (isFrozen x) $ do
                  xs <- allMetasList . jMetaType . mvJudgement <$> lookupLocalMeta x
                  mapM_ unfreezeMeta (x : xs)
                checkAlias t info i name e mc
            | otherwise -> do -- Warn about abstract alias (will never work!)
              -- Ulf, 2021-11-18, #5620: Don't warn if the meta is solved. A more intuitive solution
              -- would be to not treat definitions with solved meta types as aliases, but in mutual
              -- blocks you might actually have solved the type of an alias by the time you get to
              -- the definition. See test/Succeed/SizeInfinity.agda for an example where this
              -- happens.
              whenM (isOpenMeta <$> lookupMetaInstantiation x) $
                setCurrentRange i $ warning $ MissingTypeSignatureForOpaque name (Info.defOpaque i)
              checkFunDef' t info Nothing Nothing i name cs
          _ -> checkFunDef' t info Nothing Nothing i name cs

        -- If it's a macro check that it ends in Term → TC ⊤
        let ismacro = isMacro . theDef $ def
        when (ismacro || Info.defMacro i == MacroDef) $ checkMacroType t
    `catchIlltypedPatternBlockedOnMeta` \ (err, blocker) -> do
        reportSDoc "tc.def" 20 $ vcat $
          [ "checking function definition got stuck on: " <+> pretty blocker ]
        modifySignature $ updateDefinition name $ updateDefBlocked $ const $ Blocked blocker ()
        addConstraint blocker $ CheckFunDef i name cs err

checkMacroType :: Type -> TCM ()
checkMacroType t = do
  TelV tel tr <- telView t

  let telList = telToList tel
      resType = abstract (telFromList (drop (length telList - 1) telList)) tr
  expectedType <- el primAgdaTerm --> el (primAgdaTCM <#> primLevelZero <@> primUnit)
  equalType resType expectedType
    `catchError` \ _ -> typeError $ MacroResultTypeMismatch expectedType

-- | A single clause without arguments and without type signature is an alias.
isAlias :: [A.Clause] -> Type -> Maybe (A.Expr, Maybe C.Expr, MetaId)
isAlias cs t =
        case trivialClause cs of
          -- if we have just one clause without pattern matching and
          -- without a type signature, then infer, to allow
          -- "aliases" for things starting with hidden abstractions
          Just (e, mc) | Just x <- isMeta (unEl t) -> Just (e, mc, x)
          _ -> Nothing
  where
    isMeta (MetaV x _) = Just x
    isMeta _           = Nothing
    trivialClause [A.Clause (A.LHS i (A.LHSHead f [])) _ (A.RHS e mc) wh _]
      | null wh     = Just (e, mc)
    trivialClause _ = Nothing

-- | Check a trivial definition of the form @f = e@
checkAlias :: Type -> ArgInfo -> A.DefInfo -> QName -> A.Expr -> Maybe C.Expr -> TCM ()
checkAlias t ai i name e mc =
  let clause = A.Clause { clauseLHS          = A.SpineLHS (LHSInfo (getRange i) NoEllipsis) name []
                        , clauseStrippedPats = []
                        , clauseRHS          = A.RHS e mc
                        , clauseWhereDecls   = A.noWhereDecls
                        , clauseCatchall     = False } in
  atClause name 0 t Nothing clause $ do
  reportSDoc "tc.def.alias" 10 $ "checkAlias" <+> vcat
    [ text (prettyShow name) <+> colon  <+> prettyTCM t
    , text (prettyShow name) <+> equals <+> prettyTCM e
    ]

  -- Infer the type of the rhs.
  -- Andreas, 2018-06-09, issue #2170.
  -- The context will only be resurrected if we have --irrelevant-projections.
  v <- applyModalityToContextFunBody ai $ checkDontExpandLast CmpLeq e t

  reportSDoc "tc.def.alias" 20 $ "checkAlias: finished checking"

  solveSizeConstraints DontDefaultToInfty

  v <- instantiateFull v  -- if we omit this, we loop (stdlib: Relation.Binary.Sum)
    -- or the termination checker might stumble over levels in sorts
    -- that cannot be converted to expressions without the level built-ins
    -- (test/succeed/Issue655.agda)

  -- compute body modification for irrelevant definitions, see issue 610
  let bodyMod = applyWhen (isIrrelevant ai) dontCare

  -- Add the definition
  fun <- emptyFunctionData
  addConstant' name ai t $ FunctionDefn $
    set funMacro_ (Info.defMacro i == MacroDef) $
    set funAbstr_ (Info.defAbstract i) $
      fun { _funClauses   = [ Clause  -- trivial clause @name = v@
              { clauseLHSRange    = getRange i
              , clauseFullRange   = getRange i
              , clauseTel         = EmptyTel
              , namedClausePats   = []
              , clauseBody        = Just $ bodyMod v
              , clauseType        = Just $ Arg ai t
              , clauseCatchall    = False
              , clauseRecursive   = Nothing   -- we don't know yet
              , clauseUnreachable = Just False
              , clauseEllipsis    = NoEllipsis
              , clauseWhereModule = Nothing
              } ]
          , _funCompiled  = Just $ Done [] $ bodyMod v
          , _funSplitTree = Just $ SplittingDone 0
          , _funOpaque    = Info.defOpaque i
          }

  -- Andreas, 2017-01-01, issue #2372:
  -- Add the definition to the instance table, if needed, to update its type.
  case Info.defInstance i of
    InstanceDef _r -> setCurrentRange name $ addTypedInstance name t
      -- Put highlighting on the name only;
      -- @(getRange (r, name))@ does not give good results.
    NotInstanceDef -> pure ()

  reportSDoc "tc.def.alias" 20 $ "checkAlias: leaving"


-- | Type check a definition by pattern matching.
checkFunDef' :: Type             -- ^ the type we expect the function to have
             -> ArgInfo          -- ^ is it irrelevant (for instance)
             -> Maybe ExtLamInfo -- ^ does the definition come from an extended lambda
                                 --   (if so, we need to know some stuff about lambda-lifted args)
             -> Maybe QName      -- ^ is it a with function (if so, what's the name of the parent function)
             -> A.DefInfo        -- ^ range info
             -> QName            -- ^ the name of the function
             -> [A.Clause]       -- ^ the clauses to check
             -> TCM ()
checkFunDef' t ai extlam with i name cs =
  checkFunDefS t ai extlam with i name Nothing cs

-- | Type check a definition by pattern matching.
checkFunDefS :: Type             -- ^ the type we expect the function to have
             -> ArgInfo          -- ^ is it irrelevant (for instance)
             -> Maybe ExtLamInfo -- ^ does the definition come from an extended lambda
                                 --   (if so, we need to know some stuff about lambda-lifted args)
             -> Maybe QName      -- ^ is it a with function (if so, what's the name of the parent function)
             -> A.DefInfo        -- ^ range info
             -> QName            -- ^ the name of the function
             -> Maybe (Substitution, Map Name LetBinding)
                                 -- ^ substitution (from with abstraction) that needs to be applied
                                 --   to module parameters, and let-bindings inherited from parent
                                 --   clause
             -> [A.Clause]       -- ^ the clauses to check
             -> TCM ()
checkFunDefS t ai extlam with i name withSubAndLets cs = do

    traceCall (CheckFunDefCall (getRange i) name cs True) $ do
        reportSDoc "tc.def.fun" 10 $
          sep [ "checking body of" <+> prettyTCM name
              , nest 2 $ ":" <+> prettyTCM t
              , nest 2 $ "full type:" <+> (prettyTCM . defType =<< getConstInfo name)
              ]

        reportSDoc "tc.def.fun" 70 $
          sep $ "clauses:" : map (nest 2 . text . show . A.deepUnscope) cs

        cs <- return $ map A.lhsToSpine cs

        reportSDoc "tc.def.fun" 70 $
          sep $ "spine clauses:" : map (nest 2 . text . show . A.deepUnscope) cs

        -- Ensure that all clauses have the same number of trailing hidden patterns
        -- This is necessary since trailing implicits are no longer eagerly inserted.
        -- Andreas, 2013-10-13
        -- Since we have flexible function arity, it is no longer necessary
        -- to patch clauses to same arity
        -- cs <- trailingImplicits t cs

        -- Check the clauses
        cs <- traceCall NoHighlighting $ do -- To avoid flicker.
          forM (zip cs [0..]) $ \ (c, clauseNo) -> do
            atClause name clauseNo t (fst <$> withSubAndLets) c $ do
              (c,b) <- applyModalityToContextFunBody ai $ do
                checkClause t withSubAndLets c
              -- Andreas, 2013-11-23 do not solve size constraints here yet
              -- in case we are checking the body of an extended lambda.
              -- 2014-04-24: The size solver requires each clause to be
              -- checked individually, since otherwise we get constraints
              -- in typing contexts which are not prefixes of each other.
              whenNothing extlam $ solveSizeConstraints DontDefaultToInfty
              -- Andreas, 2013-10-27 add clause as soon it is type-checked
              -- TODO: instantiateFull?
              inTopContext $ addClauses name [c]
              return (c,b)

        (cs, CPC isOneIxs) <- return $ (second mconcat . unzip) cs

        -- If there is a partial match ("system"), no proper (co)pattern matching is allowed.
        let isSystem = not . null $ isOneIxs
        when isSystem do
          -- allow VarP and ConP i0/i1 fallThrough = yes, DotP
          let pss = map namedClausePats cs
              allowed = \case
                VarP{} -> True
                -- pattern inserted by splitPartial
                ConP _ cpi [] | conPFallThrough cpi -> True
                DotP{} -> True
                _      -> False
          unless (all (all $ allowed . namedArg) pss) $
            typeError PatternInSystem

        reportSDoc "tc.def.fun" 70 $ inTopContext $ do
          sep $ "checked clauses:" : map (nest 2 . text . show) cs

        -- After checking, remove the clauses again.
        -- (Otherwise, @checkInjectivity@ loops for issue 801).
        modifyFunClauses name (const [])

        reportSDoc "tc.cc" 25 $ inTopContext $ do
          sep [ "clauses before injectivity test"
              , nest 2 $ prettyTCM $ map (QNamed name) cs  -- broken, reify (QNamed n cl) expect cl to live at top level
              ]
        reportSDoc "tc.cc" 60 $ inTopContext $ do
          sep [ "raw clauses: "
              , nest 2 $ sep $ map (text . show . QNamed name) cs
              ]

        -- Needed to calculate the proper fullType below.
        applyPolarityToContext ai $ applyCohesionToContext ai $ do

        -- Systems have their own coverage and "coherence" check, we
        -- also add an absurd clause for the cases not needed.
        (cs,sys) <- if not isSystem then return (cs, empty) else do
                 fullType <- flip abstract t <$> getContextTelescope
                 sys <- inTopContext $ checkSystemCoverage name (IntSet.toList isOneIxs) fullType cs
                 tel <- getContextTelescope
                 let c = Clause
                       { clauseFullRange = noRange
                       , clauseLHSRange  = noRange
                       , clauseTel       = tel
                       , namedClausePats = teleNamedArgs tel
                       , clauseBody      = Nothing
                       , clauseType      = Just (defaultArg t)
                       , clauseCatchall    = False
                       , clauseRecursive   = Just False
                       , clauseUnreachable = Just False
                       , clauseEllipsis    = NoEllipsis
                       , clauseWhereModule = Nothing
                       }
                 return (cs ++ [c], pure sys)

        -- Annotate the clauses with which arguments are actually used.
        cs <- instantiateFull {- =<< mapM rebindClause -} cs
        -- Andreas, 2010-11-12
        -- rebindClause is the identity, and instantiateFull eta-contracts
        -- removing this eta-contraction fixes issue 361
        -- however, Data.Star.Decoration.gmapAll no longer type-checks
        -- possibly due to missing eta-contraction!?

        -- Inline copattern record constructors on demand.
        cs <- concat <$> do
          forM cs $ \ cl -> do
            (cls, nonExactSplit) <- runChangeT $ recordRHSToCopatterns cl
            when nonExactSplit do
              -- If we inlined a non-eta constructor,
              -- issue a warning that the clause does not hold as definitional equality.
              warning $ InlineNoExactSplit name cl
            return cls

        -- Check if the function is injective.
        -- Andreas, 2015-07-01 we do it here in order to resolve metas
        -- in mutual definitions, e.g. the U/El definition in succeed/Issue439.agda
        -- We do it again for the mutual block after termination checking, see Rules.Decl.
        reportSLn "tc.inj.def" 20 $ "checkFunDef': checking injectivity..."
        inv <- Bench.billTo [Bench.Injectivity] $
          checkInjectivity name cs

        reportSDoc "tc.cc" 15 $ inTopContext $ do
          sep [ "clauses before compilation"
              , nest 2 $ sep $ map (prettyTCM . QNamed name) cs
              ]

        reportSDoc "tc.cc.raw" 65 $ do
          sep [ "clauses before compilation"
              , nest 2 $ sep $ map (text . show) cs
              ]

        -- add clauses for the coverage (& confluence) checker (needs to reduce)
        inTopContext $ addClauses name cs

        reportSDoc "tc.cc.type" 60 $ "  type   : " <+> (text . prettyShow) t
        reportSDoc "tc.cc.type" 60 $ "  context: " <+> (text . prettyShow =<< getContextTelescope)

        fullType <- flip telePi t <$> getContextTelescope

        reportSLn  "tc.cc.type" 80 $ show fullType

        -- Coverage check and compile the clauses
        (mst, _recordExpressionBecameCopatternLHS, cc) <- Bench.billTo [Bench.Coverage] $
          unsafeInTopContext $ compileClauses (if isSystem then Nothing else (Just (name, fullType)))
                                        cs
        -- Andreas, 2019-10-21 (see also issue #4142):
        -- We ignore whether the clause compilation turned some
        -- record expressions into copatterns
        -- (_recordExpressionsBecameCopatternLHS),
        -- since the defCopatternLHS flag is anyway set by traversing
        -- the compiled clauses looking for a copattern match
        -- (hasProjectionPatterns).

        -- Clause compilation runs the coverage checker, which might add
        -- some extra clauses.
        cs <- defClauses <$> getConstInfo name

        reportSDoc "tc.cc" 60 $ inTopContext $ do
          sep [ "compiled clauses of" <+> prettyTCM name
              , nest 2 $ pretty cc
              ]

        -- The macro tag might be on the type signature
        ismacro <- isMacro . theDef <$> getConstInfo name

        covering <- funCovering . theDef <$> getConstInfo name

        -- Add the definition
        inTopContext $ addConstant name =<< do

          reportSDoc "tc.def.fun.clauses" 15 $ inTopContext $ do
            vcat [ "final clauses for" <+> prettyTCM name <+>  ":"
                 , nest 2 $ vcat $ map (prettyTCM . QNamed name) cs
                 ]

          -- If there was a pragma for this definition, we can set the
          -- funTerminates field directly.
          fun  <- emptyFunctionData
          defn <- autoInline $ FunctionDefn $
           set funMacro_ (ismacro || Info.defMacro i == MacroDef) $
           set funAbstr_ (Info.defAbstract i) $
           fun
             { _funClauses        = cs
             , _funCompiled       = Just cc
             , _funSplitTree      = mst
             , _funInv            = inv
             , _funOpaque         = Info.defOpaque i
             , _funExtLam         = (\ e -> e { extLamSys = sys }) <$> extlam
             , _funWith           = with
             , _funCovering       = covering
             }
          lang <- getLanguage
          useTerPragma $
            updateDefCopatternLHS (const $ hasProjectionPatterns cc) $
            (defaultDefn ai name fullType lang defn)

        reportSDoc "tc.def.fun" 10 $ do
          sep [ "added " <+> prettyTCM name <+> ":"
              , nest 2 $ prettyTCM . defType =<< getConstInfo name
              ]

        -- Jesper, 2019-05-30: if the constructors used in the
        -- lhs of a clause have rewrite rules, we need to check
        -- confluence here
        whenJustM (optConfluenceCheck <$> pragmaOptions) $ \confChk -> inTopContext $
          checkConfluenceOfClauses confChk name

-- | Set 'funTerminates' according to termination info in 'TCEnv',
--   which comes from a possible termination pragma.
useTerPragma :: Definition -> TCM Definition
useTerPragma def@Defn{ defName = name, theDef = fun@Function{}} = do
  tc <- viewTC eTerminationCheck
  let terminates = case tc of
        NonTerminating -> Just False
        Terminating    -> Just True
        _              -> Nothing
  reportS "tc.fundef" 30 $
    [ "funTerminates of " ++ prettyShow name ++ " set to " ++ show terminates
    , "  tc = " ++ show tc
    ]
  return $ def { theDef = fun { funTerminates = terminates }}
useTerPragma def = return def

-- | Modify all the LHSCore of the given RHS.
-- (Used to insert patterns for @rewrite@ or the inspect idiom)
mapLHSCores :: (A.LHSCore -> A.LHSCore) -> (A.RHS -> A.RHS)
mapLHSCores f = \case
  A.WithRHS aux es cs -> A.WithRHS aux es $ for cs $
    \ (A.Clause (A.LHS info core)     spats rhs                 ds catchall) ->
       A.Clause (A.LHS info (f core)) spats (mapLHSCores f rhs) ds catchall
  A.RewriteRHS qes spats rhs wh -> A.RewriteRHS qes spats (mapLHSCores f rhs) wh
  rhs@A.AbsurdRHS -> rhs
  rhs@A.RHS{}     -> rhs

-- | Insert some names into the with-clauses LHS of the given RHS.
-- (Used for the inspect idiom)
insertNames :: List1 (Arg (Maybe A.BindName)) -> A.RHS -> A.RHS
insertNames = mapLHSCores . insertInspects

insertInspects :: List1 (Arg (Maybe A.BindName)) -> A.LHSCore -> A.LHSCore
insertInspects ps = \case
  A.LHSWith core wps [] ->
    let ps' = fmap (fmap $ fmap patOfName) ps in
    A.LHSWith core (List1.fromListSafe __IMPOSSIBLE__ $ insertIn (List1.toList ps') (List1.toList wps)) []
  -- Andreas, AIM XXXV, 2022-05-09, issue #5728:
  -- Cases other than LHSWith actually do not make sense, but let them
  -- through to get a proper error later.
  lhs -> lhs

  where

    patOfName :: A.BindName -> Arg A.Pattern
    patOfName = defaultArg . A.VarP

    insertIn :: [Arg (Maybe (Arg a))]
             -> [Arg a] -> [Arg a]
    insertIn []                 wps  = wps
    insertIn (Arg info nm : ps) (w : wps) | visible info =
      w : maybeToList nm ++ insertIn ps wps
    insertIn (Arg info nm : ps) wps       | notVisible info =
          maybeToList nm ++ insertIn ps wps
    insertIn _ _ = __IMPOSSIBLE__


-- | Insert some with-patterns into the with-clauses LHS of the given RHS.
-- (Used for @rewrite@)
insertPatterns :: List1 (Arg A.Pattern) -> A.RHS -> A.RHS
insertPatterns pats = mapLHSCores (insertPatternsLHSCore pats)

-- | Insert with-patterns before the trailing with patterns.
-- If there are none, append the with-patterns.
insertPatternsLHSCore :: List1 (Arg A.Pattern) -> A.LHSCore -> A.LHSCore
insertPatternsLHSCore pats = \case
  A.LHSWith core wps [] -> A.LHSWith core (pats <> wps) []
  core                  -> A.LHSWith core pats []

-- | Parameters for creating a @with@-function.
data WithFunctionProblem
  = NoWithFunction
  | WithFunction
    { wfParentName   :: QName                            -- ^ Parent function name.
    , wfName         :: QName                            -- ^ With function name.
    , wfParentType   :: Type                             -- ^ Type of the parent function.
    , wfParentTel    :: Telescope                        -- ^ Context of the parent patterns.
    , wfBeforeTel    :: Telescope                        -- ^ Types of arguments to the with function before the with expressions (needed vars).
    , wfAfterTel     :: Telescope                        -- ^ Types of arguments to the with function after the with expressions (unneeded vars).
    , wfExprs        :: List1 (Arg (Term, EqualityView)) -- ^ With and rewrite expressions and their types.
    , wfRHSType      :: Type                             -- ^ Type of the right hand side.
    , wfParentPats   :: [NamedArg DeBruijnPattern]       -- ^ Parent patterns.
    , wfParentParams :: Nat                              -- ^ Number of module parameters in parent patterns
    , wfPermSplit    :: Permutation                      -- ^ Permutation resulting from splitting the telescope into needed and unneeded vars.
    , wfPermParent   :: Permutation                      -- ^ Permutation reordering the variables in the parent pattern.
    , wfPermFinal    :: Permutation                      -- ^ Final permutation (including permutation for the parent clause).
    , wfClauses      :: List1 A.Clause                   -- ^ The given clauses for the with function
    , wfCallSubst    :: Substitution                     -- ^ Substitution to generate call for the parent.
    , wfLetBindings  :: Map Name LetBinding              -- ^ The let-bindings in scope of the parent (in the parent context).
    }

checkSystemCoverage
  :: QName
  -> [Int]
  -> Type
  -> [Clause]
  -> TCM System
checkSystemCoverage f [n] t cs = do
  reportSDoc "tc.sys.cover" 10 $ text (show (n , length cs)) <+> prettyTCM t
  TelV gamma t <- telViewUpTo n t
  addContext gamma $ do
  TelV (ExtendTel a _) _ <- telViewUpTo 1 t
  a <- reduce $ unEl $ unDom a

  case a of
    Def q [Apply phi] -> do
      [iz,io] <- mapM getBuiltinName' [builtinIZero, builtinIOne]
      ineg <- primINeg
      imin <- primIMin
      imax <- primIMax
      i0 <- primIZero
      i1 <- primIOne
      let
        isDir (ConP q _ []) | Just (conName q) == iz = Just False
        isDir (ConP q _ []) | Just (conName q) == io = Just True
        isDir _ = Nothing

        collectDirs :: [Int] -> [DeBruijnPattern] -> [(Int,Bool)]
        collectDirs [] [] = []
        collectDirs (i : is) (p : ps) | Just d <- isDir p = (i,d) : collectDirs is ps
                                      | otherwise         = collectDirs is ps
        collectDirs _ _ = __IMPOSSIBLE__

        dir :: (Int,Bool) -> Term
        dir (i,False) = ineg `apply` [argN $ var i]
        dir (i,True) = var i

        -- andI and orI have cases for singletons to improve error messages.
        andI, orI :: [Term] -> Term
        andI [] = i1
        andI [t] = t
        andI (t:ts) = (\ x -> imin `apply` [argN t, argN x]) $ andI ts

        orI [] = i0
        orI [t] = t
        orI (t:ts) = imax `apply` [argN t, argN (orI ts)]

      let
        pats = map (take n . map (namedThing . unArg) . namedClausePats) cs
        alphas :: [[(Int,Bool)]] -- the face maps corresponding to each clause
        alphas = map (collectDirs (downFrom n)) pats
        phis :: [Term] -- the φ terms for each clause (i.e. the alphas as terms)
        phis = map (andI . (map dir)) alphas
        psi = orI $ phis
        pcs = zip phis cs

      reportSDoc "tc.sys.cover" 20 $ fsep $ map prettyTCM pats
      interval <- primIntervalType
      reportSDoc "tc.sys.cover" 10 $ "equalTerm " <+> prettyTCM (unArg phi) <+> prettyTCM psi
      equalTerm interval (unArg phi) psi

      forM_ (initWithDefault __IMPOSSIBLE__ $
             initWithDefault __IMPOSSIBLE__ $ List.tails pcs) $ \ ((phi1,cl1):pcs') -> do
        forM_ pcs' $ \ (phi2,cl2) -> do
          phi12 <- reduce (imin `apply` [argN phi1, argN phi2])
          forallFaceMaps phi12 (\ _ _ -> __IMPOSSIBLE__) $ \_ sigma -> do
            let args = sigma `applySubst` teleArgs gamma
                t' = sigma `applySubst` t
                fromReduced (YesReduction _ x) = x
                fromReduced (NoReduction x) = ignoreBlocking x
                body cl = do
                  let extra = length (drop n $ namedClausePats cl)
                  TelV delta _ <- telViewUpTo extra t'
                  fmap (abstract delta) $ addContext delta $ do
                    fmap fromReduced $ runReduceM $
                      appDef' f (Def f []) [cl] [] (map notReduced $ raise (size delta) args ++ teleArgs delta)
            v1 <- body cl1
            v2 <- body cl2
            equalTerm t' v1 v2

      sys <- forM (zip alphas cs) $ \ (alpha,cl) -> do

            let
                -- Δ = Γ_α , Δ'α
                delta = clauseTel cl
                -- Δ ⊢ b
                Just b = clauseBody cl
                -- Δ ⊢ ps : Γ , o : [φ] , Δ'
                -- we assume that there's no pattern matching other
                -- than from the system
                ps = namedClausePats cl
                extra = length (drop (size gamma + 1) ps)
                -- size Δ'α = size Δ' = extra
                -- Γ , α ⊢ u
                takeLast n xs = drop (length xs - n) xs
                weak [] = idS
                weak (i:is) = weak is `composeS` liftS i (raiseS 1)
                tel = telFromList (takeLast extra (telToList delta))
                u = abstract tel (liftS extra (weak $ List.sort $ map fst alpha) `applySubst` b)
            return (map (first var) alpha,u)

      reportSDoc "tc.sys.cover.sys" 20 $ fsep $ prettyTCM gamma : map prettyTCM sys
      reportSDoc "tc.sys.cover.sys" 40 $ fsep $ (text . show) gamma : map (text . show) sys
      return (System gamma sys) -- gamma uses names from the type, not the patterns, could we do better?
    _ -> __IMPOSSIBLE__
checkSystemCoverage _ _ t cs = __IMPOSSIBLE__


-- * Info that is needed after all clauses have been processed.

data ClausesPostChecks = CPC
    { cpcPartialSplits :: IntSet
      -- ^ Which argument indexes have a partial split.
    }

instance Semigroup ClausesPostChecks where
  CPC xs <> CPC xs' = CPC (IntSet.union xs xs')

instance Monoid ClausesPostChecks where
  mempty  = CPC empty
  mappend = (<>)

-- | The LHS part of checkClause.
checkClauseLHS :: Type -> Maybe Substitution -> A.SpineClause -> (LHSResult -> TCM a) -> TCM a
checkClauseLHS t withSub c@(A.Clause lhs@(A.SpineLHS i x aps) strippedPats rhs0 wh catchall) ret = do
    reportSDoc "tc.lhs.top" 30 $ "Checking clause" $$ prettyA c
    () <- List1.unlessNull (trailingWithPatterns aps) $ \ withPats -> do
      typeError $ UnexpectedWithPatterns $ fmap namedArg withPats
    traceCall (CheckClause t c) $ do
      aps <- expandPatternSynonyms aps
      unless (null strippedPats) $ reportSDoc "tc.lhs.top" 50 $
        "strippedPats:" <+> vcat [ prettyA p <+> "=" <+> prettyTCM v <+> ":" <+> prettyTCM a | A.ProblemEq p v a <- strippedPats ]
      closed_t <- flip abstract t <$> getContextTelescope
      checkLeftHandSide (CheckLHS lhs) (getRange lhs) (Just x) aps t withSub strippedPats ret

-- | Type check a function clause.

checkClause
  :: Type          -- ^ Type of function defined by this clause.
  -> Maybe (Substitution, Map Name LetBinding)  -- ^ Module parameter substitution arising from with-abstraction, and inherited let-bindings.
  -> A.SpineClause -- ^ Clause.
  -> TCM (Clause, ClausesPostChecks)  -- ^ Type-checked clause

checkClause t withSubAndLets c@(A.Clause lhs@(A.SpineLHS i x aps) strippedPats rhs0 wh catchall) = do
  let withSub       = fst <$> withSubAndLets
  cxtNames <- reverse . map (fst . unDom) <$> getContext
  checkClauseLHS t withSub c $ \ lhsResult@(LHSResult npars delta ps absurdPat trhs patSubst asb psplit ixsplit) -> do

    let installInheritedLets k
          | Just (withSub, lets) <- withSubAndLets = do
            lets' <- traverse makeOpen $ applySubst (patSubst `composeS` withSub) lets
            locallyTC eLetBindings (lets' <>) k
          | otherwise = k

    installInheritedLets $ do
        -- Note that we might now be in irrelevant context,
        -- in case checkLeftHandSide walked over an irrelevant projection pattern.

        -- Subtle: checkRHS expects the function type to be the lambda lifted
        -- type. If we're checking a with-function that's already the case,
        -- otherwise we need to abstract over the module telescope.
        t' <- case withSub of
                Just{}  -> return t
                Nothing -> do
                  theta <- lookupSection (qnameModule x)
                  return $ abstract theta t

        -- At this point we should update the named dots potential with-clauses
        -- in the right-hand side. When checking a clause we expect the named
        -- dots to live in the context of the closest parent lhs, but the named
        -- dots added by buildWithFunction live in the context of the
        -- with-function arguments before pattern matching. That's what we need
        -- patSubst for.
        let rhs = updateRHS rhs0
            updateRHS rhs@A.RHS{}               = rhs
            updateRHS rhs@A.AbsurdRHS{}         = rhs
            updateRHS (A.WithRHS q es cs)       = A.WithRHS q es $ fmap updateClause cs
            updateRHS (A.RewriteRHS qes spats rhs wh) =
              A.RewriteRHS qes (applySubst patSubst spats) (updateRHS rhs) wh

            updateClause (A.Clause f spats rhs wh ca) =
              A.Clause f (applySubst patSubst spats) (updateRHS rhs) wh ca

        (body, with) <- bindAsPatterns asb $ checkWhere wh $ checkRHS i x aps t' lhsResult rhs

        -- Note that the with function doesn't necessarily share any part of
        -- the context with the parent (but withSub will take you from parent
        -- to child).

        wbody <- unsafeInTopContext $ Bench.billTo [Bench.Typing, Bench.With] $ checkWithFunction cxtNames with

        body <- return $ body `mplus` wbody

        whenM (optDoubleCheck <$> pragmaOptions) $ case body of
          Just v  -> do
            reportSDoc "tc.lhs.top" 30 $ vcat
              [ "double checking rhs"
              , nest 2 (prettyTCM v <+> " : " <+> prettyTCM (unArg trhs))
              ]
            noConstraints $ withFrozenMetas $ checkInternal v CmpLeq $ unArg trhs
          Nothing -> return ()

        reportSDoc "tc.lhs.top" 10 $ vcat
          [ "Clause before translation:"
          , nest 2 $ vcat
            [ "delta =" <+> do escapeContext impossible (size delta) $ prettyTCM delta
            , "ps    =" <+> do P.fsep <$> prettyTCMPatterns ps
            , "body  =" <+> maybe "_|_" prettyTCM body
            , "type  =" <+> prettyTCM t
            ]
          ]

        reportSDoc "tc.lhs.top" 60 $ escapeContext impossible (size delta) $ vcat
          [ "Clause before translation (raw):"
          , nest 2 $ vcat
            [ "ps    =" <+> text (show ps)
            , "body  =" <+> text (show body)
            , "type  =" <+> text (show t)
            ]
          ]

        -- compute body modification for irrelevant definitions, see issue 610
        rel <- viewTC eRelevance
        let bodyMod = applyWhen (isIrrelevant rel) (fmap dontCare)

        -- absurd clauses don't define computational behaviour, so it's fine to
        -- treat them as catchalls.
        let catchall' = catchall || isNothing body

        return $ (, CPC psplit)
          Clause { clauseLHSRange  = getRange i
                 , clauseFullRange = getRange c
                 , clauseTel       = killRange delta
                 , namedClausePats = ps
                 , clauseBody      = bodyMod body
                 , clauseType      = Just trhs
                 , clauseCatchall  = catchall'
                 , clauseRecursive   = Nothing -- we don't know yet
                 , clauseUnreachable = Nothing -- we don't know yet
                 , clauseEllipsis    = lhsEllipsis i
                 , clauseWhereModule = A.whereModule wh
                 }



-- | Generate the abstract pattern corresponding to Refl
getReflPattern :: TCM A.Pattern
getReflPattern = do
  -- Get the name of builtin REFL.
  Con reflCon _ [] <- primRefl

  reflInfo <- fmap (setOrigin Inserted) <$> getReflArgInfo reflCon
  let patInfo = ConPatInfo ConOCon patNoRange ConPatEager
  -- The REFL constructor might have an argument
  let reflArg = maybeToList $ fmap (\ ai -> Arg ai $ unnamed $ A.WildP patNoRange) reflInfo

  pure $ A.ConP patInfo (unambiguous $ conName reflCon) reflArg

-- | Type check the @with@ and @rewrite@ lhss and/or the rhs.
checkRHS
  :: LHSInfo                 -- ^ Range of lhs.
  -> QName                   -- ^ Name of function.
  -> [NamedArg A.Pattern]    -- ^ Patterns in lhs.
  -> Type                    -- ^ Top-level type of function.
  -> LHSResult               -- ^ Result of type-checking patterns
  -> A.RHS                   -- ^ Rhs to check.
  -> TCM (Maybe Term, WithFunctionProblem)
                                              -- Note: the as-bindings are already bound (in checkClause)
checkRHS i x aps t lhsResult@(LHSResult _ delta ps absurdPat trhs _ _asb _ _) rhs0 =
  handleRHS rhs0 where

  handleRHS :: A.RHS -> TCM (Maybe Term, WithFunctionProblem)
  handleRHS rhs = case rhs of
    A.RHS e _                  -> ordinaryRHS e
    A.AbsurdRHS                -> noRHS
    A.RewriteRHS eqs ps rhs wh -> rewriteEqnsRHS eqs ps rhs wh
    A.WithRHS aux es cs        -> withRHS aux es cs

  -- Ordinary case: f xs = e
  ordinaryRHS :: A.Expr -> TCM (Maybe Term, WithFunctionProblem)
  ordinaryRHS e = Bench.billTo [Bench.Typing, Bench.CheckRHS] $ do
    -- If there is an absurd pattern, we do not need a RHS. If we have
    -- one we complain, ignore it and return the same @(Nothing, NoWithFunction)@
    -- as the case dealing with @A.AbsurdRHS@.
    mv <- if absurdPat
          then Nothing <$ do setCurrentRange e $ warning AbsurdPatternRequiresAbsentRHS
          else Just <$> checkExpr e (unArg trhs)
    return (mv, NoWithFunction)

  -- Absurd case: no right hand side
  noRHS :: TCM (Maybe Term, WithFunctionProblem)
  noRHS = do
    unless absurdPat $ typeError AbsentRHSRequiresAbsurdPattern
    return (Nothing, NoWithFunction)

  -- With case: @f xs with {a} in eqa | b in eqb | {{c}} | ...; ... | ps1 = rhs1; ... | ps2 = rhs2; ...@
  -- We need to modify the patterns `ps1, ps2, ...` in the user-provided clauses
  -- to insert the {eqb} names so that the equality proofs are available on the various RHS.
  withRHS ::
       QName             -- name of the with-function
    -> List1 A.WithExpr  -- @[{a} in eqa, b in eqb, {{c}}, ...]@
    -> List1 A.Clause    -- @[(ps1 = rhs1), (ps2 = rhs), ...]@
    -> TCM (Maybe Term, WithFunctionProblem)
  withRHS aux es cs = do

    reportSDoc "tc.with.top" 15 $ vcat
      [ "TC.Rules.Def.checkclause reached A.WithRHS"
      , sep $ prettyA aux <| fmap (parens . prettyA . namedThing) es
      ]
    reportSDoc "tc.with.top" 20 $ do
      nfv <- getCurrentModuleFreeVars
      m   <- currentModule
      sep [ "with function module:" <+>
             prettyList (map prettyTCM $ mnameToList m)
          ,  text $ "free variables: " ++ show nfv
          ]

    -- Infer the types of the with expressions

    vtys <- forM es $ \ (Named nm we) -> do
              (e, ty) <- inferExprForWith we
              pure $ (<$ we) . (e,) $ case nm of
                Nothing -> OtherType ty
                Just{}  -> IdiomType ty

    let names = fmap (\ (Named nm e) -> nm <$ e) es
    cs <- forM cs $ \ c@(A.Clause (A.LHS i core) eqs rhs wh b) -> do
      let rhs'  = insertNames    names rhs
      let core' = insertInspects names core
      pure $ A.Clause (A.LHS i core') eqs rhs' wh b

    -- Andreas, 2016-01-23, Issue #1796
    -- Run the size constraint solver to improve with-abstraction
    -- in case the with-expression contains size metas.
    solveSizeConstraints DefaultToInfty

    checkWithRHS x aux t lhsResult vtys cs

  -- Rewrite case: f xs (rewrite / invert) a | b | c | ...
  rewriteEqnsRHS
    :: [A.RewriteEqn]
    -> [A.ProblemEq]
    -> A.RHS
    -> A.WhereDeclarations
    -> TCM (Maybe Term, WithFunctionProblem)

  rewriteEqnsRHS [] strippedPats rhs wh = checkWhere wh $ handleRHS rhs
      -- Case: @rewrite@
      -- Andreas, 2014-01-17, Issue 1402:
      -- If the rewrites are discarded since lhs=rhs, then
      -- we can actually have where clauses.
  rewriteEqnsRHS (r:rs) strippedPats rhs wh = case r of
    Rewrite ((qname, eq) :| qes) ->
      rewriteEqnRHS qname eq $
        List1.ifNull qes {-then-} rs {-else-} $ \ qes -> Rewrite qes : rs
    Invert qname pes -> invertEqnRHS qname pes rs
    LeftLet pes -> usingEqnRHS pes rs

    where

    -- @using@ clauses
    usingEqnRHS :: List1 (A.Pattern, A.Expr) -> [A.RewriteEqn] -> TCM (Maybe Term, WithFunctionProblem)
    usingEqnRHS pes rs = do
      let letBindings = for (List1.toList pes) $ \(p, e) -> A.LetPatBind (LetRange $ getRange e) p e
      checkLetBindings letBindings $ rewriteEqnsRHS rs strippedPats rhs wh

    -- @invert@ clauses
    invertEqnRHS :: QName -> List1 (Named A.BindName (A.Pattern,A.Expr)) -> [A.RewriteEqn] -> TCM (Maybe Term, WithFunctionProblem)
    invertEqnRHS qname pes rs = do

      let (npats, es) = List1.unzipWith (\ (Named nm (p , e)) -> (Named nm p, Named nm e)) pes
      -- Infer the types of the with expressions
      vtys <- forM es $ \ (Named nm we) -> do
        (e, ty) <- inferExprForWith (defaultArg we)
        pure $ defaultArg . (e,) $ case nm of
          Nothing -> OtherType ty
          Just{}  -> IdiomType ty

      let pats = fmap defaultArg $ sconcat $
            for npats $ \ (Named nm p) -> p :| maybe [] (\ n -> [A.VarP n]) nm

      -- Andreas, 2016-04-14, see also Issue #1796
      -- Run the size constraint solver to improve with-abstraction
      -- in case the with-expression contains size metas.
      solveSizeConstraints DefaultToInfty

      let rhs' = insertPatterns pats rhs
          (rhs'', outerWhere) -- the where clauses should go on the inner-most with
            | null rs  = (rhs', wh)
            | otherwise = (A.RewriteRHS rs strippedPats rhs' wh, A.noWhereDecls)
          -- Andreas, 2014-03-05 kill range of copied patterns
          -- since they really do not have a source location.
          cl = A.Clause (A.LHS i $ insertPatternsLHSCore pats $ A.LHSHead x $ killRange aps)
                 strippedPats rhs'' outerWhere False

      reportSDoc "tc.invert" 60 $ vcat
        [ text "invert"
        , "  rhs' = " <> (text . show) rhs'
        ]
      checkWithRHS x qname t lhsResult vtys $ singleton cl

    -- @rewrite@ clauses
    rewriteEqnRHS
      :: QName
      -> A.Expr
      -> [A.RewriteEqn]
      -> TCM (Maybe Term, WithFunctionProblem)
    rewriteEqnRHS qname eq rs = do

      -- Action for skipping this rewrite.
      -- We do not want to create unsolved metas in case of
      -- a futile rewrite with a reflexive equation.
      -- Thus, we restore the state in this case,
      -- unless the rewrite expression contains questionmarks.
      st <- getTC
      -- TODO:: recurse defined but not used
      let recurse = do
           st' <- getTC
           -- Comparing the whole stInteractionPoints maps is a bit
           -- wasteful, but we assume
           -- 1. rewriting with a reflexive equality to happen rarely,
           -- 2. especially with ?-holes in the rewrite expression
           -- 3. and a large overall number of ?s.
           let sameIP = (==) `on` (^. stInteractionPoints)
           when (sameIP st st') $ putTC st
           handleRHS $ A.RewriteRHS rs strippedPats rhs wh

      -- Get value and type of rewrite-expression.

      (proof, eqt) <- inferExpr eq

      -- Andreas, 2024-02-27, issue #7150
      -- trigger instance search to resolve instances in rewrite-expression
      solveAwakeConstraints

      -- Andreas, 2016-04-14, see also Issue #1796
      -- Run the size constraint solver to improve with-abstraction
      -- in case the with-expression contains size metas.
      solveSizeConstraints DefaultToInfty

      -- Check that the type is actually an equality (lhs ≡ rhs)
      -- and extract lhs, rhs, and their type.

      t' <- reduce =<< instantiateFull eqt
      (eqt,rewriteType,rewriteFrom,rewriteTo) <- equalityView t' >>= \case
        eqt@(EqualityType _s _eq _params (Arg _ dom) a b) -> do
          s <- sortOf dom
          return (eqt, El s dom, unArg a, unArg b)
          -- Note: the sort _s of the equality need not be the sort of the type @dom@!
        OtherType{} -> typeError $ CannotRewriteByNonEquation t'
        IdiomType{} -> typeError $ CannotRewriteByNonEquation t'

      reflPat <- getReflPattern

      -- Andreas, 2015-12-25  Issue #1740:
      -- After the fix of #520, rewriting with a reflexive equation
      -- has to be desugared as matching against refl.
      let isReflexive = tryConversion $ dontAssignMetas $
           equalTerm rewriteType rewriteFrom rewriteTo

      (pats', withExpr, withType) <- do
        ifM isReflexive
          {-then-} (return (                      reflPat :| [], proof, OtherType t'))
          {-else-} (return (A.WildP patNoRange <| reflPat :| [], proof, eqt))
      let pats = defaultArg <$> pats'

      let rhs' = insertPatterns pats rhs
          (rhs'', outerWhere) -- the where clauses should go on the inner-most with
            | null rs  = (rhs', wh)
            | otherwise = (A.RewriteRHS rs strippedPats rhs' wh, A.noWhereDecls)
          -- Andreas, 2014-03-05 kill range of copied patterns
          -- since they really do not have a source location.
          cl = A.Clause (A.LHS i $ insertPatternsLHSCore pats $ A.LHSHead x $ killRange aps)
                 strippedPats rhs'' outerWhere False

      reportSDoc "tc.rewrite" 60 $ vcat
        [ text "rewrite"
        , "  rhs' = " <> (text . show) rhs'
        ]
      checkWithRHS x qname t lhsResult (singleton $ defaultArg (withExpr, withType)) $ singleton cl

checkWithRHS
  :: QName                             -- ^ Name of function.
  -> QName                             -- ^ Name of the with-function.
  -> Type                              -- ^ Type of function.
  -> LHSResult                         -- ^ Result of type-checking patterns
  -> List1 (Arg (Term, EqualityView))  -- ^ Expressions and types of with-expressions.
  -> List1 A.Clause                    -- ^ With-clauses to check.
  -> TCM (Maybe Term, WithFunctionProblem)
                                -- Note: as-bindings already bound (in checkClause)
checkWithRHS x aux t (LHSResult npars delta ps _absurdPat trhs _ _asb _ _) vtys0 cs =
  verboseBracket "tc.with.top" 25 "checkWithRHS" $ do
    Bench.billTo [Bench.Typing, Bench.With] $ do
        withArgs <- withArguments vtys0
        let perm = fromMaybe __IMPOSSIBLE__ $ dbPatPerm ps

        reportSDoc "tc.with.top" 30 $ vcat $
          -- declared locally because we do not want to use the unzip'd thing!
          let (vs, as) = List1.unzipWith unArg vtys0 in
          [ "vs (before normalization) =" <+> prettyTCM vs
          , "as (before normalization) =" <+> prettyTCM as
          ]
        reportSDoc "tc.with.top" 45 $ vcat $
          -- declared locally because we do not want to use the unzip'd thing!
          let (vs, as) = List1.unzipWith unArg vtys0 in
          [ "vs (before norm., raw) =" <+> pretty vs
          ]
        vtys0 <- normalise vtys0

        -- Andreas, 2012-09-17: for printing delta,
        -- we should remove it from the context first
        reportSDoc "tc.with.top" 25 $ escapeContext impossible (size delta) $ vcat
          [ "delta  =" <+> prettyTCM delta
          ]
        reportSDoc "tc.with.top" 25 $ vcat $
          -- declared locally because we do not want to use the unzip'd thing!
          let (vs, as) = List1.unzipWith unArg vtys0 in
          [ "vs     =" <+> prettyTCM vs
          , "as     =" <+> prettyTCM as
          , "perm   =" <+> text (show perm)
          ]

        -- Split the telescope into the part needed to type the with arguments
        -- and all the other stuff
        let (delta1, delta2, perm', t', vtys) = splitTelForWith delta (unArg trhs) vtys0
        let finalPerm = composeP perm' perm

        reportSLn "tc.with.top" 75 $ "delta  = " ++ show delta

        -- Andreas, 2012-09-17: for printing delta,
        -- we should remove it from the context first
        reportSDoc "tc.with.top" 25 $ escapeContext impossible (size delta) $ vcat
          [ "delta1 =" <+> prettyTCM delta1
          , "delta2 =" <+> addContext delta1 (prettyTCM delta2)
          ]
        reportSDoc "tc.with.top" 25 $ vcat
          [ "perm'  =" <+> text (show perm')
          , "fPerm  =" <+> text (show finalPerm)
          ]

        -- Create the body of the original function

        -- All the context variables
        us <- getContextTerms
        let n = size us
            m = size delta
            -- First the variables bound outside this definition
            (us0, us1') = splitAt (n - m) us
            -- Then permute the rest and grab those needed to for the with arguments
            (us1, us2)  = splitAt (size delta1) $ permute perm' us1'
            -- Now stuff the with arguments in between and finish with the remaining variables
            argsS = parallelS $ reverse $ us0 ++ us1 ++ map unArg (List1.toList withArgs) ++ us2
            v         = Nothing -- generated by checkWithFunction
        -- Andreas, 2013-02-26 add with-name to signature for printing purposes
        addConstant aux =<< do
          lang <- getLanguage
          useTerPragma =<<
            defaultDefn defaultArgInfo aux __DUMMY_TYPE__ lang <$>
              emptyFunction

        reportSDoc "tc.with.top" 20 $ vcat $
          let (vs, as) = List1.unzipWith unArg vtys in
          [ "    with arguments" <+> do escapeContext impossible (size delta) $ addContext delta1 $ prettyList (fmap prettyTCM vs)
          , "             types" <+> do escapeContext impossible (size delta) $ addContext delta1 $ prettyList (fmap prettyTCM as)
          , "           context" <+> (prettyTCM =<< getContextTelescope)
          , "             delta" <+> do escapeContext impossible (size delta) $ prettyTCM delta
          , "            delta1" <+> do escapeContext impossible (size delta) $ prettyTCM delta1
          , "            delta2" <+> do escapeContext impossible (size delta) $ addContext delta1 $ prettyTCM delta2
          ]

        -- Only inherit user-written let bindings from parent clauses. Others, like @-patterns,
        -- should not be carried over.
        lets <- Map.filter ((== UserWritten) . letOrigin) <$> (traverse getOpen =<< viewTC eLetBindings)

        return (v, WithFunction x aux t delta delta1 delta2 vtys t' ps npars perm' perm finalPerm cs argsS lets)

-- | Invoked in empty context.
checkWithFunction :: [Name] -> WithFunctionProblem -> TCM (Maybe Term)
checkWithFunction _ NoWithFunction = return Nothing
checkWithFunction cxtNames (WithFunction f aux t delta delta1 delta2 vtys b qs npars perm' perm finalPerm cs argsS lets) = do
  let -- Δ₁ ws Δ₂ ⊢ withSub : Δ′    (where Δ′ is the context of the parent lhs)
      withSub :: Substitution
      withSub = let as = fmap (snd . unArg) vtys in
                liftS (size delta2) (wkS (countWithArgs as) idS)
                `composeS` renaming impossible (reverseP perm')

  reportSDoc "tc.with.top" 10 $ vcat
    [ "checkWithFunction"
    , nest 2 $ vcat $
      let (vs, as) = List1.unzipWith unArg vtys in
      [ "delta1 =" <+> prettyTCM delta1
      , "delta2 =" <+> addContext delta1 (prettyTCM delta2)
      , "t      =" <+> prettyTCM t
      , "as     =" <+> addContext delta1 (prettyTCM as)
      , "vs     =" <+> do addContext delta1 $ prettyTCM vs
      , "b      =" <+> do addContext delta1 $ addContext delta2 $ prettyTCM b
      , "qs     =" <+> do addContext delta $ prettyTCMPatternList qs
      , "perm'  =" <+> text (show perm')
      , "perm   =" <+> text (show perm)
      , "fperm  =" <+> text (show finalPerm)
      , "withSub=" <+> text (show withSub)
      ]
    ]

  -- Add the type of the auxiliary function to the signature

  -- Jesper, 2020-04-05: Currently variable generalization inserts
  -- dummy terms, we have to reduce projections to get rid of them.
  -- (see also #1332).
  let reds = SmallSet.fromList [ProjectionReductions]
  delta1 <- modifyAllowedReductions (const reds) $ normalise delta1

  -- Generate the type of the with function
  (withFunType, n) <- do
    let ps = renaming impossible (reverseP perm') `applySubst` qs
    reportSDoc "tc.with.bndry" 40 $ addContext delta1 $ addContext delta2
                                  $ text "ps =" <+> pretty ps
    let vs = iApplyVars ps
    bndry <- if null vs then return [] else do
      iz <- primIZero
      io <- primIOne
      let tm = Def f (patternsToElims ps)
      return [(i,(inplaceS i iz `applySubst` tm, inplaceS i io `applySubst` tm)) | i <- vs]
    reportSDoc "tc.with.bndry" 40 $ addContext delta1 $ addContext delta2
                                  $ text "bndry =" <+> pretty bndry
    withFunctionType delta1 vtys delta2 b bndry
  reportSDoc "tc.with.type" 10 $ sep [ "with-function type:", nest 2 $ prettyTCM withFunType ]
  reportSDoc "tc.with.type" 50 $ sep [ "with-function type:", nest 2 $ pretty withFunType ]

  call_in_parent <- do
    (TelV tel _,bs) <- telViewUpToPathBoundaryP (n + size delta) withFunType
    return $ argsS `applySubst` Def aux (teleElims tel bs)

  reportSDoc "tc.with.top" 20 $ addContext delta $ "with function call" <+> prettyTCM call_in_parent

  -- Andreas, 2013-10-21
  -- Check generated type directly in internal syntax.
  setCurrentRange cs $
    traceCall NoHighlighting $   -- To avoid flicker.
    traceCall (CheckWithFunctionType withFunType) $
    -- Jesper, 2024-07-10, issue $6841:
    -- Having an ill-typed type can lead to problems in the
    -- coverage checker, so we ensure there are no constraints here.
    noConstraints $ checkType withFunType

  -- With display forms are closed
  df <- inTopContext $ makeOpen =<< withDisplayForm f aux delta1 delta2 n qs perm' perm

  reportSLn "tc.with.top" 20 "created with display form"

  case dget df of
    Display n ts dt ->
      reportSDoc "tc.with.top" 20 $ "Display" <+> fsep
        [ text (show n)
        , prettyList $ map prettyTCM ts
        , prettyTCM dt
        ]
  addConstant aux =<< do
    lang <- getLanguage
    fun  <- emptyFunction
    useTerPragma $
      (defaultDefn defaultArgInfo aux withFunType lang fun)
        { defDisplay = [df] }
  -- solveSizeConstraints -- Andreas, 2012-10-16 does not seem necessary

  reportSDoc "tc.with.top" 10 $ sep
    [ "added with function" <+> (prettyTCM aux) <+> "of type"
    , nest 2 $ prettyTCM withFunType
    , nest 2 $ "-|" <+> (prettyTCM =<< getContextTelescope)
    ]
  reportSDoc "tc.with.top" 70 $ vcat
    [ nest 2 $ text $ "raw with func. type = " ++ show withFunType
    ]


  -- Construct the body for the with function
  cs <- return $ fmap (A.lhsToSpine) cs
  cs <- buildWithFunction cxtNames f aux t delta qs npars withSub finalPerm (size delta1) n cs
  cs <- return $ fmap (A.spineToLhs) cs

  -- #4833: inherit abstract mode from parent
  abstr <- defAbstract <$> ignoreAbstractMode (getConstInfo f)

  -- Check the with function
  let info = Info.mkDefInfo (nameConcrete $ qnameName aux) noFixity' PublicAccess abstr (getRange cs)
  ai <- defArgInfo <$> getConstInfo f
  checkFunDefS withFunType ai Nothing (Just f) info aux (Just (withSub, lets)) $ List1.toList cs
  return $ Just $ call_in_parent

-- | Type check a where clause.
checkWhere
  :: A.WhereDeclarations -- ^ Where-declarations to check.
  -> TCM a               -- ^ Continuation.
  -> TCM a
checkWhere wh@(A.WhereDecls whmod whNamed ds) ret = do
  when (not whNamed) $ ensureNoNamedWhereInRefinedContext whmod
  loop ds
  where
    loop = \case
      Nothing -> ret
      -- [A.ScopedDecl scope ds] -> withScope_ scope $ loop ds  -- IMPOSSIBLE
      Just (A.Section _ e m tel ds) -> newSection e m tel $ do
          localTC (\ e -> e { envCheckingWhere = True }) $ do
            checkDecls ds
            ret
      _ -> __IMPOSSIBLE__

    -- #2897: We can't handle named where-modules in refined contexts.
    ensureNoNamedWhereInRefinedContext Nothing = return ()
    ensureNoNamedWhereInRefinedContext (Just m) = traceCall (CheckNamedWhere m) $ do
      args <- map unArg <$> (moduleParamsToApply =<< currentModule)
      unless (isWeakening args) $ do -- weakened contexts are fine
        names <- map (argNameToString . fst . unDom) . telToList <$>
                (lookupSection =<< currentModule)
        typeError $ NamedWhereModuleInRefinedContext args names
      where
        isWeakening [] = True
        isWeakening (Var i [] : args) = isWk (i - 1) args
          where
            isWk i []                = True
            isWk i (Var j [] : args) = i == j && isWk (i - 1) args
            isWk _ _ = False
        isWeakening _ = False


-- | Enter a new section during type-checking.

newSection ::
  Erased -> ModuleName -> A.GeneralizeTelescope -> TCM a -> TCM a
newSection e m gtel@(A.GeneralizeTel _ tel) cont = do
  -- If the section is erased, then hard compile-time mode is entered.
  warnForPlentyInHardCompileTimeMode e
  setHardCompileTimeModeIfErased e $ do
  reportSDoc "tc.section" 10 $
    "checking section" <+> (C.prettyErased e <$> prettyTCM m) <+>
    fsep (map prettyA tel)

  checkGeneralizeTelescope (Just m) gtel $ \ _ tel' -> do
    reportSDoc "tc.section" 10 $
      "adding section:" <+> prettyTCM m <+> text (show (size tel'))

    addSection m

    reportSDoc "tc.section" 10 $ inTopContext $
      nest 4 $ "actual tele:" <+> do prettyTCM =<< lookupSection m

    withCurrentModule m cont

-- | Set the current clause number.

atClause :: QName -> Int -> Type -> Maybe Substitution -> A.SpineClause -> TCM a -> TCM a
atClause name i t sub cl ret = do
  clo <- buildClosure ()
  localTC (\ e -> e { envClause = IPClause name i t sub cl clo }) ret
