{- |

"Injectivity", or more precisely, "constructor headedness", is a
property of functions defined by pattern matching that helps us solve
constraints involving blocked applications of such functions.
"Blocked" shall mean here that pattern matching is blocked on a meta
variable, and constructor headedness lets us learn more about that
meta variable.

Consider the simple example:
@
  isZero : Nat -> Bool
  isZero zero    = true
  isZero (suc n) = false
@
This function is constructor-headed, meaning that all rhss are headed
by a distinct constructor.  Thus, on a constraint like
@
  isZero ?X = false : Bool
@
involving an application of @isZero@ that is blocked on meta variable @?X@,
we can exploit injectivity and learn that @?X = suc ?Y@ for a new
meta-variable @?Y@.

Which functions qualify for injectivity?

1. The function needs to have at least one non-absurd clause that has
a proper match, meaning that the function can actually be blocked on a
meta.  Proper matches are these patterns:

  - data constructor (@ConP@, but not record constructor)
  - literal (@LitP@)
  - HIT-patterns (@DefP@)

Projection patterns (@ProjP@) are excluded because metas cannot occupy their place!

2. All the clauses that satisfy (1.) need to be headed by a distinct constructor.

-}

module Agda.TypeChecking.Injectivity where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Fail
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.Traversable hiding (for)
import Data.Semigroup ((<>))

import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Irrelevance (isIrrelevantOrPropM)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Warnings

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Pretty ( prettyShow )

import Agda.Utils.Impossible

headSymbol :: Term -> TCM (Maybe TermHead)
headSymbol v = do -- ignoreAbstractMode $ do
  -- Andreas, 2013-02-18 ignoreAbstractMode leads to information leakage

  v <- constructorForm =<< ignoreBlocking <$> reduceHead v
  case v of
    Def f _ -> do
      let yes = return $ Just $ ConsHead f
          no  = return $ Nothing
      def <- theDef <$> do ignoreAbstractMode $ getConstInfo f
        -- Andreas, 2013-02-18
        -- if we do not ignoreAbstractMode here, abstract Functions get turned
        -- into Axioms, but we want to distinguish these.
      case def of
        Datatype{}  -> yes
        Record{}    -> yes
        DataOrRecSig{} -> yes
        Axiom{}     -> do
          reportSLn "tc.inj.axiom" 50 $ "headSymbol: " ++ prettyShow f ++ " is an Axiom."
          -- Don't treat axioms in the current mutual block
          -- as constructors (they might have definitions we
          -- don't know about yet).
          caseMaybeM (asksTC envMutualBlock) yes $ \ mb -> do
            fs <- mutualNames <$> lookupMutualBlock mb
            if Set.member f fs then no else yes
        Function{}    -> no
        Primitive{}   -> no
        PrimitiveSort{} -> no
        GeneralizableVar{} -> __IMPOSSIBLE__
        Constructor{} -> __IMPOSSIBLE__
        AbstractDefn{}-> __IMPOSSIBLE__
    -- Andreas, 2019-07-10, issue #3900: canonicalName needs ignoreAbstractMode
    Con c _ _ -> ignoreAbstractMode $ do
                 q <- canonicalName (conName c)
                 ifM (isPathCons q) (return Nothing) $
                     {- else -}     return $ Just $ ConsHead q
    Sort _  -> return (Just SortHead)
    Pi _ _  -> return (Just PiHead)
    Var i [] -> return (Just $ VarHead i) -- Only naked variables. Otherwise substituting a neutral term is not guaranteed to stay neutral.
    Lit _   -> return Nothing -- TODO: LitHead (for literals with no constructorForm)
    Lam{}   -> return Nothing
    Var{}   -> return Nothing
    Level{} -> return Nothing
    MetaV{} -> return Nothing
    DontCare{} -> return Nothing
    Dummy s _ -> __IMPOSSIBLE_VERBOSE__ s

-- | Do a full whnf and treat neutral terms as rigid. Used on the arguments to
--   an injective functions and to the right-hand side.
headSymbol'
  :: (PureTCM m, MonadError TCErr m)
  => Term -> m (Maybe TermHead)
headSymbol' v = do
  v <- traverse constructorForm =<< reduceB v
  case v of
    Blocked{} -> return Nothing
    NotBlocked _ v -> case v of
      Def g _    -> return $ Just $ ConsHead g
      Con c _ _  -> return $ Just $ ConsHead $ conName c
      Var i _    -> return $ Just (VarHead i)
      Sort _     -> return $ Just SortHead
      Pi _ _     -> return $ Just PiHead
      Lit _      -> return Nothing
      Lam{}      -> return Nothing
      Level{}    -> return Nothing
      DontCare{} -> return Nothing
      MetaV{}    -> __IMPOSSIBLE__
      Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s

-- | Does deBruijn variable i correspond to a top-level argument, and if so
--   which one (index from the left).
topLevelArg :: Clause -> Int -> Maybe TermHead
topLevelArg Clause{ namedClausePats = ps } i =
  case [ n | (n, VarP _ (DBPatVar _ j)) <- zip [0..] $ map namedArg ps, i == j ] of
    []    -> Nothing
    [n]   -> Just (VarHead n)
    _:_:_ -> __IMPOSSIBLE__

-- | Join a list of inversion maps.
joinHeadMaps :: [InversionMap c] -> InversionMap c
joinHeadMaps = Map.unionsWith (<>)

-- | Update the heads of an inversion map.
updateHeads :: Monad m => (TermHead -> [c] -> m TermHead) -> InversionMap c -> m (InversionMap c)
updateHeads f m = joinHeadMaps <$> mapM f' (Map.toList m)
  where f' (h, c) = (`Map.singleton` c) <$> f h c

checkInjectivity :: QName -> [Clause] -> TCM FunctionInverse
checkInjectivity f cs0
  | not (any properlyMatchingClause cs) = do
      reportSLn "tc.inj.check.pointless" 35 $
        "Injectivity of " ++ prettyShow (A.qnameToConcrete f) ++ " would be pointless."
      return NotInjective
  | otherwise = checkInjectivity' f cs
  where
    -- We can filter out absurd clauses.
    cs = filter (isJust . clauseBody) cs0
    -- We cannot filter out clauses that have no proper match, because
    -- these could be catch-all clauses.
    -- However, we need at least one proper match to get injectivity started.
    properlyMatchingClause =
      any (properlyMatching' False False . namedArg) . namedClausePats

-- | Precondition: all the given clauses are non-absurd and contain a proper match.
checkInjectivity' :: QName -> [Clause] -> TCM FunctionInverse
checkInjectivity' f cs = fromMaybe NotInjective <.> runMaybeT $ do
  reportSLn "tc.inj.check" 40 $ "Checking injectivity of " ++ prettyShow f

  let varToArg :: Clause -> TermHead -> MaybeT TCM TermHead
      varToArg c (VarHead i) = MaybeT $ return $ topLevelArg c i
      varToArg _ h           = return h

  -- We don't need to consider absurd clauses
  let computeHead c | hasDefP (namedClausePats c) = return []
      -- hasDefP clauses are skipped, these matter only for --cubical, in which case the function will behave as NotInjective.
      computeHead c@Clause{ clauseBody = Just body , clauseType = Just tbody } = do
        maybeIrr <- fromRight (const True) <.> runBlocked $ isIrrelevantOrPropM tbody
        h <- if maybeIrr then return UnknownHead else
          varToArg c =<< do
            lift $ fromMaybe UnknownHead <$> do
              addContext (clauseTel c) $
                headSymbol body
        return [Map.singleton h [c]]
      computeHead _ = return []

  hdMap <- joinHeadMaps . concat <$> mapM computeHead cs

  case Map.lookup UnknownHead hdMap of
    Just (_:_:_) -> empty -- More than one unknown head: we can't really do anything in that case.
    _            -> return ()

  reportSLn  "tc.inj.check" 20 $ prettyShow f ++ " is potentially injective."
  reportSDoc "tc.inj.check" 30 $ nest 2 $ vcat $
    for (Map.toList hdMap) $ \ (h, uc) ->
      text (prettyShow h) <+> "-->" <+>
      case uc of
        [c] -> prettyTCM $ map namedArg $ namedClausePats c
        _   -> "(multiple clauses)"
  let cond | any (hasDefP . namedClausePats) cs = UnlessCubical
           | otherwise                          = AlwaysInjective
  return $ Inverse cond hdMap

-- | If a clause is over-applied we can't trust the head (Issue 2944). For
--   instance, the clause might be `f ps = u , v` and the actual call `f vs
--   .fst`. In this case the head will be the head of `u` rather than `_,_`.
checkOverapplication
  :: forall m. (HasConstInfo m)
  => Elims -> InversionMap Clause -> m (InversionMap Clause)
checkOverapplication es = updateHeads overapplied
  where
    overapplied :: TermHead -> [Clause] -> m TermHead
    overapplied h cs | all (not . isOverapplied) cs = return h
    overapplied h cs = ifM (isSuperRigid h) (return h) (return UnknownHead)

    -- A super-rigid head is one that can't be eliminated. Crucially, this is
    -- applied after instantiateVars, so VarHeads are really bound variables.
    isSuperRigid SortHead     = return True
    isSuperRigid PiHead       = return True
    isSuperRigid VarHead{}    = return True
    isSuperRigid UnknownHead  = return True -- or False, doesn't matter
    isSuperRigid (ConsHead q) = do
      def <- getConstInfo q
      return $ case theDef def of
        Axiom{}        -> True
        DataOrRecSig{} -> True
        AbstractDefn{} -> True
        Function{}     -> False
        Datatype{}     -> True
        Record{}       -> True
        Constructor{conSrcCon = ConHead{ conDataRecord = d, conFields = fs }}
                       -> d == IsData || null fs   -- Record constructors can be eliminated by projections
        Primitive{}    -> False
        PrimitiveSort{} -> __IMPOSSIBLE__
        GeneralizableVar{} -> __IMPOSSIBLE__


    isOverapplied Clause{ namedClausePats = ps } = length es > length ps

-- | Turn variable heads, referring to top-level argument positions, into
--   proper heads. These might still be `VarHead`, but in that case they refer to
--   deBruijn variables. Checks that the instantiated heads are still rigid and
--   distinct.
instantiateVarHeads
  :: forall m c. (PureTCM m, MonadError TCErr m)
  => QName -> Elims -> InversionMap c -> m (Maybe (InversionMap c))
instantiateVarHeads f es m = runMaybeT $ updateHeads (const . instHead) m
  where
    instHead :: TermHead -> MaybeT m TermHead
    instHead h@(VarHead i)
      | Just (Apply arg) <- es !!! i = MaybeT $ headSymbol' (unArg arg)
      | otherwise = empty   -- impossible?
    instHead h = return h

-- | Argument should be in weak head normal form.
functionInverse
  :: (PureTCM m, MonadError TCErr m)
  => Term -> m InvView
functionInverse = \case
  Def f es -> do
    inv <- defInverse <$> getConstInfo f
    cubical <- optCubical <$> pragmaOptions
    case inv of
      NotInjective -> return NoInv
      Inverse UnlessCubical m | isJust cubical -> return NoInv
      Inverse w m -> maybe NoInv (Inv f es) <$> (traverse (checkOverapplication es) =<< instantiateVarHeads f es m)
        -- NB: Invertible functions are never classified as
        --     projection-like, so this is fine, we are not
        --     missing parameters.  (Andreas, 2013-11-01)
  _ -> return NoInv

data InvView = Inv QName [Elim] (InversionMap Clause)
             | NoInv

-- | Precondition: The first term must be blocked on the given meta and the second must be neutral.
useInjectivity :: MonadConversion m => CompareDirection -> Blocker -> CompareAs -> Term -> Term -> m ()
useInjectivity dir blocker ty blk neu = locallyTC eInjectivityDepth succ $ do
  inv <- functionInverse blk
  -- Injectivity might cause non-termination for unsatisfiable constraints
  -- (#431, #3067). Look at the number of active problems and the injectivity
  -- depth to detect this.
  nProblems <- Set.size <$> viewTC eActiveProblems
  injDepth  <- viewTC eInjectivityDepth
  let depth = max nProblems injDepth
  maxDepth  <- maxInversionDepth
  case inv of
    NoInv            -> fallback  -- not invertible
    Inv f blkArgs hdMap
      | depth > maxDepth -> warning (InversionDepthReached f) >> fallback
      | otherwise -> do
      reportSDoc "tc.inj.use" 30 $ fsep $
        pwords "useInjectivity on" ++
        [ prettyTCM blk, prettyTCM cmp, prettyTCM neu, prettyTCM ty]
      let canReduceToSelf = Map.member (ConsHead f) hdMap || Map.member UnknownHead hdMap
      case neu of
        -- f us == f vs  <=>  us == vs
        -- Crucially, this relies on `f vs` being neutral and only works
        -- if `f` is not a possible head for `f us`.
        Def f' neuArgs | f == f', not canReduceToSelf -> do
          fTy <- defType <$> getConstInfo f
          reportSDoc "tc.inj.use" 20 $ vcat
            [ fsep (pwords "comparing application of injective function" ++ [prettyTCM f] ++
                  pwords "at")
            , nest 2 $ fsep $ punctuate comma $ map prettyTCM blkArgs
            , nest 2 $ fsep $ punctuate comma $ map prettyTCM neuArgs
            , nest 2 $ "and type" <+> prettyTCM fTy
            ]
          fs  <- getForcedArgs f
          pol <- getPolarity' cmp f
          reportSDoc "tc.inj.invert.success" 20 $ hsep ["Successful spine comparison of", prettyTCM f]
          app (compareElims pol fs fTy (Def f [])) blkArgs neuArgs

        -- f us == c vs
        --    Find the clause unique clause `f ps` with head `c` and unify
        --    us == ps  with fresh metas for the pattern variables of ps.
        --    If there's no such clause we can safely throw an error.
        _ -> headSymbol' neu >>= \ case
          Nothing -> do
            reportSDoc "tc.inj.use" 20 $ fsep $
              pwords "no head symbol found for" ++ [prettyTCM neu] ++ pwords ", so not inverting"
            fallback
          Just (ConsHead f') | f == f', canReduceToSelf -> do
            reportSDoc "tc.inj.use" 20 $ fsep $
              pwords "head symbol" ++ [prettyTCM f'] ++ pwords "can reduce to self, so not inverting"
            fallback
                                    -- We can't invert in this case, since we can't
                                    -- tell the difference between a solution that makes
                                    -- the blocked term neutral and one that makes progress.
          Just hd -> invertFunction cmp blk inv hd fallback err success
            where err = typeError $ app (\ u v -> UnequalTerms cmp u v ty) blk neu
  where
    fallback     = addConstraint blocker $ app (ValueCmp cmp ty) blk neu
    success blk' = app (compareAs cmp ty) blk' neu

    cmpApp :: (Comparison, (a -> a -> b) -> a -> a -> b)
    cmpApp = case dir of
      DirEq -> (CmpEq, id)
      DirLeq -> (CmpLeq, id)
      DirGeq -> (CmpLeq, flip)
    (cmp, app) = cmpApp

-- | The second argument should be a blocked application and the third argument
--   the inverse of the applied function.
invertFunction
  :: MonadConversion m
  => Comparison -> Term -> InvView -> TermHead -> m () -> m () -> (Term -> m ()) -> m ()
invertFunction _ _ NoInv _ fallback _ _ = fallback
invertFunction cmp blk (Inv f blkArgs hdMap) hd fallback err success = do
    fTy <- defType <$> getConstInfo f
    reportSDoc "tc.inj.use" 20 $ vcat
      [ "inverting injective function" <?> hsep [prettyTCM f, ":", prettyTCM fTy]
      , "for" <?> pretty hd
      , nest 2 $ "args =" <+> prettyList (map prettyTCM blkArgs)
      ]                         -- Clauses with unknown heads are also possible candidates
    case fromMaybe [] $ Map.lookup hd hdMap <> Map.lookup UnknownHead hdMap of
      [] -> err
      _:_:_ -> fallback
      [cl@Clause{ clauseTel  = tel }] -> speculateMetas fallback $ do
          let ps   = clausePats cl
              perm = fromMaybe __IMPOSSIBLE__ $ clausePerm cl
          -- These are what dot patterns should be instantiated at
          ms <- map unArg <$> newTelMeta tel
          reportSDoc "tc.inj.invert" 20 $ vcat
            [ "meta patterns" <+> prettyList (map prettyTCM ms)
            , "  perm =" <+> text (show perm)
            , "  tel  =" <+> prettyTCM tel
            , "  ps   =" <+> prettyList (map (text . show) ps)
            ]
          -- and this is the order the variables occur in the patterns
          let msAux = permute (invertP __IMPOSSIBLE__ $ compactP perm) ms
          let sub   = parallelS (reverse ms)
          margs <- runReaderT (evalStateT (mapM metaElim ps) msAux) sub
          reportSDoc "tc.inj.invert" 20 $ vcat
            [ "inversion"
            , nest 2 $ vcat
              [ "lhs  =" <+> prettyTCM margs
              , "rhs  =" <+> prettyTCM blkArgs
              , "type =" <+> prettyTCM fTy
              ]
            ]
          -- Since we do not care for the value of non-variant metas here,
          -- we can treat 'Nonvariant' as 'Invariant'.
          -- That ensures these metas do not remain unsolved.
          pol <- purgeNonvariant <$> getPolarity' cmp f
          fs  <- getForcedArgs f
          -- The clause might not give as many patterns as there
          -- are arguments (point-free style definitions).
          let blkArgs' = take (length margs) blkArgs
          compareElims pol fs fTy (Def f []) margs blkArgs'

          -- Check that we made progress.
          r <- liftReduce $ unfoldDefinitionStep False (Def f []) f blkArgs
          case r of
            YesReduction _ blk' -> do
              reportSDoc "tc.inj.invert.success" 20 $ hsep ["Successful inversion of", prettyTCM f, "at", pretty hd]
              KeepMetas <$ success blk'
            NoReduction{}       -> do
              reportSDoc "tc.inj.invert" 30 $ vcat
                [ "aborting inversion;" <+> prettyTCM blk
                , "does not reduce"
                ]
              return RollBackMetas
  where
    nextMeta :: (MonadState [Term] m, MonadFail m) => m Term
    nextMeta = do
      m : ms <- get
      put ms
      return m

    dotP :: MonadReader Substitution m => Term -> m Term
    dotP v = do
      sub <- ask
      return $ applySubst sub v

    metaElim
      :: (MonadState [Term] m, MonadReader Substitution m, HasConstInfo m, MonadFail m)
      => Arg DeBruijnPattern -> m Elim
    metaElim (Arg _ (ProjP o p))  = Proj o <$> getOriginalProjection p
    metaElim (Arg info p)         = Apply . Arg info <$> metaPat p

    metaArgs
      :: (MonadState [Term] m, MonadReader Substitution m, MonadFail m)
      => [NamedArg DeBruijnPattern] -> m Args
    metaArgs args = mapM (traverse $ metaPat . namedThing) args

    metaPat
      :: (MonadState [Term] m, MonadReader Substitution m, MonadFail m)
      => DeBruijnPattern -> m Term
    metaPat (DotP _ v)       = dotP v
    metaPat (VarP _ _)       = nextMeta
    metaPat (IApplyP{})      = nextMeta
    metaPat (ConP c mt args) = Con c (fromConPatternInfo mt) . map Apply <$> metaArgs args
    metaPat (DefP o q args)  = Def q . map Apply <$> metaArgs args
    metaPat (LitP _ l)       = return $ Lit l
    metaPat ProjP{}          = __IMPOSSIBLE__

forcePiUsingInjectivity :: Type -> TCM Type
forcePiUsingInjectivity t = reduceB t >>= \ case
    Blocked _ blkTy -> do
      let blk = unEl blkTy
      inv <- functionInverse blk
      blkTy <$ invertFunction CmpEq blk inv PiHead fallback err success
    NotBlocked _ t -> return t
  where
    fallback  = return ()
    err       = typeError (ShouldBePi t)
    success _ = return ()
