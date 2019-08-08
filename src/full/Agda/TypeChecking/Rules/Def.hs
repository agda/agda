{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Def where

import Prelude hiding ( mapM, null )

import Control.Arrow (first,second)
import Control.Monad.State hiding (forM, mapM)

import Data.Function
import qualified Data.List as List
import Data.Maybe
import Data.Traversable (forM, mapM)
import Data.Semigroup (Semigroup((<>)))

import Agda.Interaction.Options

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Position
import Agda.Syntax.Abstract.Pattern as A
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern as I
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Fixity
import Agda.Syntax.Info

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
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
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.SizedTypes.Solve
import Agda.TypeChecking.Rewriting.Confluence
import Agda.TypeChecking.CompiledClause (CompiledClauses'(..), hasProjectionPatterns)
import Agda.TypeChecking.CompiledClause.Compile
import Agda.TypeChecking.Primitive hiding (Nat)

import Agda.TypeChecking.Rules.Term
import Agda.TypeChecking.Rules.LHS                 ( checkLeftHandSide, LHSResult(..), bindAsPatterns )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl ( checkDecls )

import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Size

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Definitions by pattern matching
---------------------------------------------------------------------------

checkFunDef :: Delayed -> Info.DefInfo -> QName -> [A.Clause] -> TCM ()
checkFunDef delayed i name cs = do
        -- Get the type and relevance of the function
        def <- instantiateDef =<< getConstInfo name
        let t    = defType def
        let info = getArgInfo def
        case isAlias cs t of
          Just (e, mc, x) ->
            traceCall (CheckFunDefCall (getRange i) name cs) $ do
              -- Andreas, 2012-11-22: if the alias is in an abstract block
              -- it has been frozen.  We unfreeze it to enable type inference.
              -- See issue 729.
              whenM (isFrozen x) $ unfreezeMeta x
              checkAlias t info delayed i name e mc
          _ -> checkFunDef' t info delayed Nothing Nothing i name cs

        -- If it's a macro check that it ends in Term → TC ⊤
        let ismacro = isMacro . theDef $ def
        when (ismacro || Info.defMacro i == MacroDef) $ checkMacroType t
    `catchIlltypedPatternBlockedOnMeta` \ (err, x) -> do
        reportSDoc "tc.def" 20 $ vcat $
          [ "checking function definition got stuck on meta: " <+> text (show x) ]
        addConstraint $ CheckFunDef delayed i name cs

checkMacroType :: Type -> TCM ()
checkMacroType t = do
  t' <- normalise t
  TelV tel tr <- telView t'

  let telList = telToList tel
      resType = abstract (telFromList (drop (length telList - 1) telList)) tr
  expectedType <- el primAgdaTerm --> el (primAgdaTCM <#> primLevelZero <@> primUnit)
  equalType resType expectedType
    `catchError` \ _ -> typeError . GenericDocError =<< sep [ "Result type of a macro must be"
                                                            , nest 2 $ prettyTCM expectedType ]

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
    trivialClause [A.Clause (A.LHS i (A.LHSHead f [])) _ (A.RHS e mc) (A.WhereDecls _ []) _] = Just (e, mc)
    trivialClause _ = Nothing

-- | Check a trivial definition of the form @f = e@
checkAlias :: Type -> ArgInfo -> Delayed -> Info.DefInfo -> QName -> A.Expr -> Maybe C.Expr -> TCM ()
checkAlias t ai delayed i name e mc = atClause name 0 (A.RHS e mc) $ do
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
  let bodyMod = case getRelevance ai of
        Irrelevant -> dontCare
        _          -> id

  -- Add the definition
  addConstant name $ defaultDefn ai name t
                   $ set funMacro (Info.defMacro i == MacroDef) $
                     emptyFunction
                      { funClauses = [ Clause  -- trivial clause @name = v@
                          { clauseLHSRange  = getRange i
                          , clauseFullRange = getRange i
                          , clauseTel       = EmptyTel
                          , namedClausePats = []
                          , clauseBody      = Just $ bodyMod v
                          , clauseType      = Just $ Arg ai t
                          , clauseCatchall  = False
                          , clauseUnreachable = Just False
                          } ]
                      , funCompiled = Just $ Done [] $ bodyMod v
                      , funSplitTree = Just $ SplittingDone 0
                      , funDelayed  = delayed
                      , funAbstr    = Info.defAbstract i
                      }

  -- Andreas, 2017-01-01, issue #2372:
  -- Add the definition to the instance table, if needed, to update its type.
  when (Info.defInstance i == InstanceDef) $ do
    addTypedInstance name t

  reportSDoc "tc.def.alias" 20 $ "checkAlias: leaving"


-- | Type check a definition by pattern matching.
checkFunDef' :: Type             -- ^ the type we expect the function to have
             -> ArgInfo        -- ^ is it irrelevant (for instance)
             -> Delayed          -- ^ are the clauses delayed (not unfolded willy-nilly)
             -> Maybe ExtLamInfo -- ^ does the definition come from an extended lambda
                                 --   (if so, we need to know some stuff about lambda-lifted args)
             -> Maybe QName      -- ^ is it a with function (if so, what's the name of the parent function)
             -> Info.DefInfo     -- ^ range info
             -> QName            -- ^ the name of the function
             -> [A.Clause]       -- ^ the clauses to check
             -> TCM ()
checkFunDef' t ai delayed extlam with i name cs =
  checkFunDefS t ai delayed extlam with i name Nothing cs

-- | Type check a definition by pattern matching.
checkFunDefS :: Type             -- ^ the type we expect the function to have
             -> ArgInfo        -- ^ is it irrelevant (for instance)
             -> Delayed          -- ^ are the clauses delayed (not unfolded willy-nilly)
             -> Maybe ExtLamInfo -- ^ does the definition come from an extended lambda
                                 --   (if so, we need to know some stuff about lambda-lifted args)
             -> Maybe QName      -- ^ is it a with function (if so, what's the name of the parent function)
             -> Info.DefInfo     -- ^ range info
             -> QName            -- ^ the name of the function
             -> Maybe Substitution -- ^ substitution (from with abstraction) that needs to be applied to module parameters
             -> [A.Clause]       -- ^ the clauses to check
             -> TCM ()
checkFunDefS t ai delayed extlam with i name withSub cs = do

    traceCall (CheckFunDefCall (getRange i) name cs) $ do
        reportSDoc "tc.def.fun" 10 $
          sep [ "checking body of" <+> prettyTCM name
              , nest 2 $ ":" <+> prettyTCM t
              , nest 2 $ "full type:" <+> (prettyTCM . defType =<< getConstInfo name)
              ]

        reportSDoc "tc.def.fun" 70 $
          sep $ [ "clauses:" ] ++ map (nest 2 . text . show . A.deepUnscope) cs

        cs <- return $ map A.lhsToSpine cs

        reportSDoc "tc.def.fun" 70 $
          sep $ [ "spine clauses:" ] ++ map (nest 2 . text . show . A.deepUnscope) cs

        -- Ensure that all clauses have the same number of trailing hidden patterns
        -- This is necessary since trailing implicits are no longer eagerly inserted.
        -- Andreas, 2013-10-13
        -- Since we have flexible function arity, it is no longer necessary
        -- to patch clauses to same arity
        -- cs <- trailingImplicits t cs

        -- Check the clauses
        cs <- traceCall NoHighlighting $ do -- To avoid flicker.
          forM (zip cs [0..]) $ \ (c, clauseNo) -> do
            atClause name clauseNo (A.clauseRHS c) $ do
              (c,b) <- applyModalityToContextFunBody ai $ do
                checkClause t withSub c
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

        let isSystem = not . null $ isOneIxs

        canBeSystem <- do
          -- allow VarP and ConP i0/i1 fallThrough = yes, DotP
          let pss = map namedClausePats cs
              allowed p = case p of
                VarP{} -> True
                -- pattern inserted by splitPartial
                ConP _ cpi [] | conPFallThrough cpi -> True
                DotP{} -> True
                _      -> False
          return $! all (allowed . namedArg) (concat pss)
        when isSystem $ unless canBeSystem $
          typeError $ GenericError "no pattern matching or path copatterns in systems!"


        reportSDoc "tc.def.fun" 70 $ inTopContext $ do
          sep $ [ "checked clauses:" ] ++ map (nest 2 . text . show) cs

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
        applyCohesionToContext ai $ do

        -- Systems have their own coverage and "coherence" check, we
        -- also add an absurd clause for the cases not needed.
        (cs,sys) <- if not isSystem then return (cs, Nothing) else do
                 fullType <- flip abstract t <$> getContextTelescope
                 sys <- inTopContext $ checkSystemCoverage name isOneIxs fullType cs
                 tel <- getContextTelescope
                 let c = Clause
                       { clauseFullRange = noRange
                       , clauseLHSRange  = noRange
                       , clauseTel = tel
                       , namedClausePats = teleNamedArgs tel
                       , clauseBody = Nothing
                       , clauseType = Just (defaultArg t)
                       , clauseCatchall = False
                       , clauseUnreachable = Just False
                       }
                 return (cs ++ [c], Just sys)

        -- Annotate the clauses with which arguments are actually used.
        cs <- instantiateFull {- =<< mapM rebindClause -} cs
        -- Andreas, 2010-11-12
        -- rebindClause is the identity, and instantiateFull eta-contracts
        -- removing this eta-contraction fixes issue 361
        -- however, Data.Star.Decoration.gmapAll no longer type-checks
        -- possibly due to missing eta-contraction!?

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
        (mst, cc) <- Bench.billTo [Bench.Coverage] $
          inTopContext $ compileClauses (if isSystem then Nothing else (Just (name, fullType)))
                                        cs

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

        -- Jesper, 2019-05-30: if the constructors used in the
        -- lhs of a clause have rewrite rules, we need to check
        -- confluence here
        whenM (optConfluenceCheck <$> pragmaOptions) $ inTopContext $
          forM_ (zip cs [0..]) $ \(c , clauseNo) ->
            checkConfluenceOfClause name clauseNo c

        -- Add the definition
        inTopContext $ addConstant name =<< do
          -- If there was a pragma for this definition, we can set the
          -- funTerminates field directly.
          defn <- autoInline $
             set funMacro (ismacro || Info.defMacro i == MacroDef) $
             emptyFunction
             { funClauses        = cs
             , funCompiled       = Just cc
             , funSplitTree      = mst
             , funDelayed        = delayed
             , funInv            = inv
             , funAbstr          = Info.defAbstract i
             , funExtLam         = (\ e -> e { extLamSys = sys }) <$> extlam
             , funWith           = with
             , funCovering       = covering
             }
          useTerPragma $
            updateDefCopatternLHS (const $ hasProjectionPatterns cc) $
            defaultDefn ai name fullType defn

        reportSDoc "tc.def.fun" 10 $ do
          sep [ "added " <+> prettyTCM name <+> ":"
              , nest 2 $ prettyTCM . defType =<< getConstInfo name
              ]

-- | Set 'funTerminates' according to termination info in 'TCEnv',
--   which comes from a possible termination pragma.
useTerPragma :: Definition -> TCM Definition
useTerPragma def@Defn{ defName = name, theDef = fun@Function{}} = do
  tc <- asksTC envTerminationCheck
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


-- | Insert some with-patterns into the with-clauses LHS of the given RHS.
-- (Used for @rewrite@.)
insertPatterns :: [A.Pattern] -> A.RHS -> A.RHS
insertPatterns pats = \case
  A.WithRHS aux es cs -> A.WithRHS aux es $ for cs $
    \ (A.Clause (A.LHS info core)                              spats rhs                       ds catchall) ->
       A.Clause (A.LHS info (insertPatternsLHSCore pats core)) spats (insertPatterns pats rhs) ds catchall
  A.RewriteRHS qes spats rhs wh -> A.RewriteRHS qes spats (insertPatterns pats rhs) wh
  rhs@A.AbsurdRHS -> rhs
  rhs@A.RHS{}     -> rhs

-- | Insert with-patterns before the trailing with patterns.
-- If there are none, append the with-patterns.
insertPatternsLHSCore :: [A.Pattern] -> A.LHSCore -> A.LHSCore
insertPatternsLHSCore pats = \case
  A.LHSWith core wps [] -> A.LHSWith core (pats ++ wps) []
  core                  -> A.LHSWith core pats []

-- | Parameters for creating a @with@-function.
data WithFunctionProblem
  = NoWithFunction
  | WithFunction
    { wfParentName :: QName                -- ^ Parent function name.
    , wfName       :: QName                -- ^ With function name.
    , wfParentType :: Type                 -- ^ Type of the parent function.
    , wfParentTel  :: Telescope            -- ^ Context of the parent patterns.
    , wfBeforeTel  :: Telescope            -- ^ Types of arguments to the with function before the with expressions (needed vars).
    , wfAfterTel   :: Telescope            -- ^ Types of arguments to the with function after the with expressions (unneeded vars).
    , wfExprs      :: [Term]               -- ^ With and rewrite expressions.
    , wfExprTypes  :: [EqualityView]       -- ^ Types of the with and rewrite expressions.
    , wfRHSType    :: Type                 -- ^ Type of the right hand side.
    , wfParentPats :: [NamedArg DeBruijnPattern] -- ^ Parent patterns.
    , wfParentParams :: Nat                -- ^ Number of module parameters in parent patterns
    , wfPermSplit  :: Permutation          -- ^ Permutation resulting from splitting the telescope into needed and unneeded vars.
    , wfPermParent :: Permutation          -- ^ Permutation reordering the variables in the parent pattern.
    , wfPermFinal  :: Permutation          -- ^ Final permutation (including permutation for the parent clause).
    , wfClauses    :: [A.Clause]           -- ^ The given clauses for the with function
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
        phis = map andI $ map (map dir) alphas
        psi = orI $ phis
        pcs = zip phis cs
        boolToI True = i1
        boolToI False = i0

      reportSDoc "tc.sys.cover" 20 $ fsep $ map prettyTCM pats
      interval <- elInf primInterval
      reportSDoc "tc.sys.cover" 10 $ "equalTerm " <+> prettyTCM (unArg phi) <+> prettyTCM psi
      equalTerm interval (unArg phi) psi

      forM_ (init $ init $ List.tails pcs) $ \ ((phi1,cl1):pcs') -> do
        forM_ pcs' $ \ (phi2,cl2) -> do
          phi12 <- reduce (imin `apply` [argN phi1, argN phi2])
          forallFaceMaps phi12 (\ _ _ -> __IMPOSSIBLE__) $ \ sigma -> do
            let args = sigma `applySubst` teleArgs gamma
                t' = sigma `applySubst` t
                fromReduced (YesReduction _ x) = x
                fromReduced (NoReduction x) = ignoreBlocking x
                body cl = do
                  let extra = length (drop n $ namedClausePats cl)
                  TelV delta _ <- telViewUpTo extra t'
                  fmap (abstract delta) $ addContext delta $ do
                    fmap fromReduced $ runReduceM $
                      appDef' (Def f []) [cl] [] (map notReduced $ raise (size delta) args ++ teleArgs delta)
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
    { cpcPartialSplits :: [Int]
      -- ^ Which argument indexes have a partial split.
    }

instance Semigroup ClausesPostChecks where
  (<>) (CPC xs) (CPC xs') = CPC (List.nub $ mappend xs xs')

instance Monoid ClausesPostChecks where
  mempty  = CPC []
  mappend = (<>)

-- | Type check a function clause.

checkClause
  :: Type          -- ^ Type of function defined by this clause.
  -> Maybe Substitution  -- ^ Module parameter substitution arising from with-abstraction.
  -> A.SpineClause -- ^ Clause.
  -> TCM (Clause,ClausesPostChecks)  -- ^ Type-checked clause

checkClause t withSub c@(A.Clause lhs@(A.SpineLHS i x aps) strippedPats rhs0 wh catchall) = do
    reportSDoc "tc.lhs.top" 30 $ "Checking clause" $$ prettyA c
    unlessNull (trailingWithPatterns aps) $ \ withPats -> do
      typeError $ UnexpectedWithPatterns $ map namedArg withPats
    traceCall (CheckClause t c) $ do
      aps <- expandPatternSynonyms aps
      cxtNames <- reverse . map (fst . unDom) <$> getContext
      when (not $ null strippedPats) $ reportSDoc "tc.lhs.top" 50 $
        "strippedPats:" <+> vcat [ prettyA p <+> "=" <+> prettyTCM v <+> ":" <+> prettyTCM a | A.ProblemEq p v a <- strippedPats ]
      closed_t <- flip abstract t <$> getContextTelescope
      checkLeftHandSide (CheckLHS lhs) (Just x) aps t withSub strippedPats $ \ lhsResult@(LHSResult npars delta ps absurdPat trhs patSubst asb psplit) -> do
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
            updateRHS (A.WithRHS q es cs)       = A.WithRHS q es (map updateClause cs)
            updateRHS (A.RewriteRHS qes spats rhs wh) =
              A.RewriteRHS qes (applySubst patSubst spats) (updateRHS rhs) wh

            updateClause (A.Clause f spats rhs wh ca) =
              A.Clause f (applySubst patSubst spats) (updateRHS rhs) wh ca

        (body, with) <- bindAsPatterns asb $ checkWhere wh $ checkRHS i x aps t' lhsResult rhs

        -- Note that the with function doesn't necessarily share any part of
        -- the context with the parent (but withSub will take you from parent
        -- to child).

        inTopContext $ Bench.billTo [Bench.Typing, Bench.With] $ checkWithFunction cxtNames with

        whenM (optDoubleCheck <$> pragmaOptions) $ case body of
          Just v  -> do
            reportSDoc "tc.lhs.top" 30 $ vcat
              [ "double checking rhs"
              , nest 2 (prettyTCM v <+> " : " <+> prettyTCM (unArg trhs))
              ]
            noConstraints $ dontAssignMetas $ checkInternal v $ unArg trhs
          Nothing -> return ()

        reportSDoc "tc.lhs.top" 10 $ vcat
          [ "Clause before translation:"
          , nest 2 $ vcat
            [ "delta =" <+> do escapeContext (size delta) $ prettyTCM delta
            , "ps    =" <+> do P.fsep <$> prettyTCMPatterns ps
            , "body  =" <+> maybe "_|_" prettyTCM body
            , "type  =" <+> prettyTCM t
            ]
          ]

        reportSDoc "tc.lhs.top" 60 $ escapeContext (size delta) $ vcat
          [ "Clause before translation (raw):"
          , nest 2 $ vcat
            [ "ps    =" <+> text (show ps)
            , "body  =" <+> text (show body)
            , "type  =" <+> text (show t)
            ]
          ]

        -- check naturality wrt the interval.
        let
          iApplyVars :: [NamedArg DeBruijnPattern] -> [(Int, (Term,Term))]
          iApplyVars ps = flip concatMap (map namedArg ps) $ \case
                             IApplyP _ t u x -> [(dbPatVarIndex x,(t,u))]
                             VarP{} -> []
                             ProjP{}-> []
                             LitP{} -> []
                             DotP{} -> []
                             DefP _ _ ps -> iApplyVars ps
                             ConP _ _ ps -> iApplyVars ps

        -- compute body modification for irrelevant definitions, see issue 610
        rel <- asksTC getRelevance
        let bodyMod body = case rel of
              Irrelevant -> dontCare <$> body
              _          -> body

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
                 , clauseUnreachable = Nothing -- we don't know yet
                 }

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
checkRHS i x aps t lhsResult@(LHSResult _ delta ps absurdPat trhs _ _asb _) rhs0 =
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
          then Nothing <$ setCurrentRange e (warning $ AbsurdPatternRequiresNoRHS ps)
          else Just <$> checkExpr e (unArg trhs)
    return (mv, NoWithFunction)

  -- Absurd case: no right hand side
  noRHS :: TCM (Maybe Term, WithFunctionProblem)
  noRHS = do
    unless absurdPat $ typeError $ NoRHSRequiresAbsurdPattern aps
    return (Nothing, NoWithFunction)


  -- With case: @f xs with a | b | c | ...; ... | ps1 = rhs1; ... | ps2 = rhs2; ...@
  -- This is mostly a wrapper around @checkWithRHS@
  withRHS :: QName       -- ^ name of the with-function
          -> [A.Expr]    -- ^ @[a, b, c, ...]@
          -> [A.Clause]  -- ^ @[(ps1 = rhs1), (ps2 = rhs), ...]@
          -> TCM (Maybe Term, WithFunctionProblem)
  withRHS aux es cs = do

    reportSDoc "tc.with.top" 15 $ vcat
      [ "TC.Rules.Def.checkclause reached A.WithRHS"
      , sep $ prettyA aux : map (parens . prettyA) es
      ]
    reportSDoc "tc.with.top" 20 $ do
      nfv <- getCurrentModuleFreeVars
      m   <- currentModule
      sep [ "with function module:" <+>
             prettyList (map prettyTCM $ mnameToList m)
          ,  text $ "free variables: " ++ show nfv
          ]

    -- Infer the types of the with expressions
    (vs0, as) <- unzip <$> mapM inferExprForWith es

    -- Andreas, 2016-01-23, Issue #1796
    -- Run the size constraint solver to improve with-abstraction
    -- in case the with-expression contains size metas.
    solveSizeConstraints DefaultToInfty

    checkWithRHS x aux t lhsResult vs0 (map OtherType as) cs

  -- Rewrite case: f xs (rewrite / invert) a | b | c | ...
  rewriteEqnsRHS :: [A.RewriteEqn] -> [A.ProblemEq] -> A.RHS -> A.WhereDeclarations -> TCM (Maybe Term, WithFunctionProblem)
  rewriteEqnsRHS [] strippedPats rhs wh = checkWhere wh $ handleRHS rhs
      -- Case: @rewrite@
      -- Andreas, 2014-01-17, Issue 1402:
      -- If the rewrites are discarded since lhs=rhs, then
      -- we can actually have where clauses.
  rewriteEqnsRHS (r:rs) strippedPats rhs wh = case r of
    Rewrite ((qname, eq) : qes) ->
      rewriteEqnRHS qname eq (case qes of { [] -> rs; _ -> Rewrite qes : rs })
    Invert ((pat, (qname, expr)) : pqes) ->
      invertEqnRHS qname pat expr (case pqes of { [] -> rs; _ -> Invert pqes : rs })
    -- Invariant: these lists are non-empty
    Rewrite [] -> __IMPOSSIBLE__
    Invert [] -> __IMPOSSIBLE__

    where

    -- @invert@ clauses
    invertEqnRHS :: QName -> A.Pattern -> A.Expr
                 -> [A.RewriteEqn] -> TCM (Maybe Term, WithFunctionProblem)
    invertEqnRHS qname pat expr rs = do

      (withExpr, ty) <- inferExpr expr
      let pats     = [pat]
      let withType = OtherType ty

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
      checkWithRHS x qname t lhsResult [withExpr] [withType] [cl]

    -- @rewrite@ clauses
    rewriteEqnRHS :: QName -> A.Expr
                  -> [A.RewriteEqn] -> TCM (Maybe Term, WithFunctionProblem)
    rewriteEqnRHS qname eq rs = do

      -- Action for skipping this rewrite.
      -- We do not want to create unsolved metas in case of
      -- a futile rewrite with a reflexive equation.
      -- Thus, we restore the state in this case,
      -- unless the rewrite expression contains questionmarks.
      st <- getTC
      let recurse = do
           st' <- getTC
           -- Comparing the whole stInteractionPoints maps is a bit
           -- wasteful, but we assume
           -- 1. rewriting with a reflexive equality to happen rarely,
           -- 2. especially with ?-holes in the rewrite expression
           -- 3. and a large overall number of ?s.
           let sameIP = (==) `on` (^.stInteractionPoints)
           when (sameIP st st') $ putTC st
           handleRHS $ A.RewriteRHS rs strippedPats rhs wh

      -- Get value and type of rewrite-expression.

      (proof, eqt) <- inferExpr eq

      -- Andreas, 2016-04-14, see also Issue #1796
      -- Run the size constraint solver to improve with-abstraction
      -- in case the with-expression contains size metas.
      solveSizeConstraints DefaultToInfty

      -- Check that the type is actually an equality (lhs ≡ rhs)
      -- and extract lhs, rhs, and their type.

      t' <- reduce =<< instantiateFull eqt
      (eqt,rewriteType,rewriteFrom,rewriteTo) <- equalityView t' >>= \case
        eqt@(EqualityType _s _eq _params (Arg _ dom) a b) -> do
          s <- inferSort dom
          return (eqt, El s dom, unArg a, unArg b)
          -- Note: the sort _s of the equality need not be the sort of the type @dom@!
        OtherType{} -> typeError . GenericDocError =<< do
          "Cannot rewrite by equation of type" <+> prettyTCM t'

      -- Get the name of builtin REFL.

      Con reflCon _ [] <- primRefl
      reflInfo <- fmap (setOrigin Inserted) <$> getReflArgInfo reflCon

      -- Andreas, 2017-01-11:
      -- The test for refl is obsolete after fixes of #520 and #1740.
      -- -- Andreas, 2014-05-17  Issue 1110:
      -- -- Rewriting with @refl@ has no effect, but gives an
      -- -- incomprehensible error message about the generated
      -- -- with clause. Thus, we rather do simply nothing if
      -- -- rewriting with @refl@ is attempted.
      -- let isReflProof = do
      --      v <- reduce proof
      --      case v of
      --        Con c _ [] | c == reflCon -> return True
      --        _ -> return False
      -- ifM isReflProof recurse $ {- else -} do

      -- Process 'rewrite' clause like a suitable 'with' clause.

      -- The REFL constructor might have an argument
      let reflPat  = A.ConP (ConPatInfo ConOCon patNoRange ConPatEager) (unambiguous $ conName reflCon) $
            maybeToList $ fmap (\ ai -> Arg ai $ unnamed $ A.WildP patNoRange) reflInfo

      -- Andreas, 2015-12-25  Issue #1740:
      -- After the fix of #520, rewriting with a reflexive equation
      -- has to be desugared as matching against refl.
      let isReflexive = tryConversion $ dontAssignMetas $
           equalTerm rewriteType rewriteFrom rewriteTo

      (pats, withExpr, withType) <- do
        ifM isReflexive
          {-then-} (return ([ reflPat ], proof, OtherType t'))
          {-else-} (return ([ A.WildP patNoRange, reflPat ], proof, eqt))

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
      checkWithRHS x qname t lhsResult [withExpr] [withType] [cl]

checkWithRHS
  :: QName                   -- ^ Name of function.
  -> QName                   -- ^ Name of the with-function.
  -> Type                    -- ^ Type of function.
  -> LHSResult               -- ^ Result of type-checking patterns
  -> [Term]                  -- ^ With-expressions.
  -> [EqualityView]          -- ^ Types of with-expressions.
  -> [A.Clause]              -- ^ With-clauses to check.
  -> TCM (Maybe Term, WithFunctionProblem)
                                -- Note: as-bindings already bound (in checkClause)
checkWithRHS x aux t (LHSResult npars delta ps _absurdPat trhs _ _asb _) vs0 as cs =
  Bench.billTo [Bench.Typing, Bench.With] $ do
        let withArgs = withArguments vs0 as
            perm = fromMaybe __IMPOSSIBLE__ $ dbPatPerm ps
        (vs, as)  <- normalise (vs0, as)

        -- Andreas, 2012-09-17: for printing delta,
        -- we should remove it from the context first
        reportSDoc "tc.with.top" 25 $ escapeContext (size delta) $ vcat
          [ "delta  =" <+> prettyTCM delta
          ]
        reportSDoc "tc.with.top" 25 $ vcat
          [ "vs     =" <+> prettyTCM vs
          , "as     =" <+> prettyTCM as
          , "perm   =" <+> text (show perm)
          ]

        -- Split the telescope into the part needed to type the with arguments
        -- and all the other stuff
        (delta1, delta2, perm', t', as, vs) <- return $
          splitTelForWith delta (unArg trhs) as vs
        let finalPerm = composeP perm' perm

        reportSLn "tc.with.top" 75 $ "delta  = " ++ show delta

        -- Andreas, 2012-09-17: for printing delta,
        -- we should remove it from the context first
        reportSDoc "tc.with.top" 25 $ escapeContext (size delta) $ vcat
          [ "delta1 =" <+> prettyTCM delta1
          , "delta2 =" <+> addContext delta1 (prettyTCM delta2)
          ]
        reportSDoc "tc.with.top" 25 $ vcat
          [ "perm'  =" <+> text (show perm')
          , "fPerm  =" <+> text (show finalPerm)
          ]

        -- Create the body of the original function

        -- All the context variables
        us <- getContextArgs
        let n = size us
            m = size delta
            -- First the variables bound outside this definition
            (us0, us1') = splitAt (n - m) us
            -- Then permute the rest and grab those needed to for the with arguments
            (us1, us2)  = splitAt (size delta1) $ permute perm' us1'
            -- Now stuff the with arguments in between and finish with the remaining variables
            v    = Def aux $ map Apply $ us0 ++ us1 ++ map defaultArg withArgs ++ us2
        -- Andreas, 2013-02-26 add with-name to signature for printing purposes
        addConstant aux =<< do
          useTerPragma $ defaultDefn defaultArgInfo aux __DUMMY_TYPE__ emptyFunction

        -- Andreas, 2013-02-26 separate msgs to see which goes wrong
        reportSDoc "tc.with.top" 20 $
          "    with arguments" <+> do escapeContext (size delta) $ addContext delta1 $ prettyList (map prettyTCM vs)
        reportSDoc "tc.with.top" 20 $
          "             types" <+> do escapeContext (size delta) $ addContext delta1 $ prettyList (map prettyTCM as)
        reportSDoc "tc.with.top" 20 $
          "with function call" <+> prettyTCM v
        reportSDoc "tc.with.top" 20 $
          "           context" <+> (prettyTCM =<< getContextTelescope)
        reportSDoc "tc.with.top" 20 $
          "             delta" <+> do escapeContext (size delta) $ prettyTCM delta
        reportSDoc "tc.with.top" 20 $
          "            delta1" <+> do escapeContext (size delta) $ prettyTCM delta1
        reportSDoc "tc.with.top" 20 $
          "            delta2" <+> do escapeContext (size delta) $ addContext delta1 $ prettyTCM delta2
        reportSDoc "tc.with.top" 20 $
          "              body" <+> prettyTCM v

        return (Just v, WithFunction x aux t delta delta1 delta2 vs as t' ps npars perm' perm finalPerm cs)

-- | Invoked in empty context.
checkWithFunction :: [Name] -> WithFunctionProblem -> TCM ()
checkWithFunction _ NoWithFunction = return ()
checkWithFunction cxtNames (WithFunction f aux t delta delta1 delta2 vs as b qs npars perm' perm finalPerm cs) = do

  let -- Δ₁ ws Δ₂ ⊢ withSub : Δ′    (where Δ′ is the context of the parent lhs)
      withSub :: Substitution
      withSub = liftS (size delta2) (wkS (countWithArgs as) idS) `composeS` renaming __IMPOSSIBLE__ (reverseP perm')

  reportSDoc "tc.with.top" 10 $ vcat
    [ "checkWithFunction"
    , nest 2 $ vcat
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

  -- Generate the type of the with function
  delta1 <- normalise delta1 -- Issue 1332: checkInternal is picky about argInfo
                             -- but module application is sloppy.
                             -- We normalise to get rid of Def's coming
                             -- from module applications.
  (withFunType, n) <- withFunctionType delta1 vs as delta2 b
  reportSDoc "tc.with.type" 10 $ sep [ "with-function type:", nest 2 $ prettyTCM withFunType ]
  reportSDoc "tc.with.type" 50 $ sep [ "with-function type:", nest 2 $ pretty withFunType ]

  -- Andreas, 2013-10-21
  -- Check generated type directly in internal syntax.
  setCurrentRange cs $
    traceCall NoHighlighting $   -- To avoid flicker.
    traceCall (CheckWithFunctionType withFunType) $
    checkType withFunType

  -- With display forms are closed
  df <- safeInTopContext $ makeOpen =<< withDisplayForm f aux delta1 delta2 n qs perm' perm

  reportSLn "tc.with.top" 20 "created with display form"

  case dget df of
    Display n ts dt ->
      reportSDoc "tc.with.top" 20 $ "Display" <+> fsep
        [ text (show n)
        , prettyList $ map prettyTCM ts
        , prettyTCM dt
        ]
  addConstant aux =<< do
    useTerPragma $ (defaultDefn defaultArgInfo aux withFunType emptyFunction)
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
  cs <- return $ map (A.lhsToSpine) cs
  cs <- buildWithFunction cxtNames f aux t delta qs npars withSub finalPerm (size delta1) n cs
  cs <- return $ map (A.spineToLhs) cs

  -- Check the with function
  checkFunDefS withFunType defaultArgInfo NotDelayed Nothing (Just f) info aux (Just withSub) cs

  where
    info = Info.mkDefInfo (nameConcrete $ qnameName aux) noFixity' PublicAccess ConcreteDef (getRange cs)

-- | Type check a where clause.
checkWhere
  :: A.WhereDeclarations -- ^ Where-declarations to check.
  -> TCM a               -- ^ Continuation.
  -> TCM a
checkWhere wh@(A.WhereDecls whmod ds) ret = do
  ensureNoNamedWhereInRefinedContext whmod
  loop ds
  where
    loop ds = case ds of
      [] -> ret
      [A.ScopedDecl scope ds] -> withScope_ scope $ loop ds
      [A.Section _ m tel ds]  -> newSection m tel $ do
          localTC (\ e -> e { envCheckingWhere = True }) $ do
            checkDecls ds
            ret
      _ -> __IMPOSSIBLE__

    -- #2897: We can't handle named where-modules in refined contexts.
    ensureNoNamedWhereInRefinedContext Nothing = return ()
    ensureNoNamedWhereInRefinedContext (Just m) = traceCall (CheckNamedWhere m) $ do
      args <- map unArg <$> (moduleParamsToApply =<< currentModule)
      unless (isWeakening args) $ -- weakened contexts are fine
        genericDocError =<< do
          names <- map (argNameToString . fst . unDom) . telToList <$>
                    (lookupSection =<< currentModule)
          let pr x v = text (x ++ " =") <+> prettyTCM v
          vcat
            [ fsep (pwords $ "Named where-modules are not allowed when module parameters have been refined by pattern matching. " ++
                             "See https://github.com/agda/agda/issues/2897.")
            , text $ "In this case the module parameter" ++
                     (if length args > 0 then "s have" else " has") ++
                     " been refined to"
            , nest 2 $ vcat (zipWith pr names args) ]
      where
        isWeakening [] = True
        isWeakening (Var i [] : args) = isWk (i - 1) args
          where
            isWk i []                = True
            isWk i (Var j [] : args) = i == j && isWk (i - 1) args
            isWk _ _ = False
        isWeakening _ = False


-- | Enter a new section during type-checking.

newSection :: ModuleName -> A.GeneralizeTelescope -> TCM a -> TCM a
newSection m gtel@(A.GeneralizeTel _ tel) cont = do
  reportSDoc "tc.section" 10 $
    "checking section" <+> prettyTCM m <+> fsep (map prettyA tel)

  checkGeneralizeTelescope gtel $ \ _ tel' -> do
    reportSDoc "tc.section" 10 $
      "adding section:" <+> prettyTCM m <+> text (show (size tel'))

    addSection m

    reportSDoc "tc.section" 10 $ inTopContext $
      nest 4 $ "actual tele:" <+> do prettyTCM =<< lookupSection m

    withCurrentModule m cont

-- | Set the current clause number.
atClause :: QName -> Int -> A.RHS -> TCM a -> TCM a
atClause name i rhs = localTC $ \ e -> e { envClause = IPClause name i rhs }
