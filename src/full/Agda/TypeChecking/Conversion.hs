{-# LANGUAGE CPP, PatternGuards #-}

module Agda.TypeChecking.Conversion where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error
import Data.Traversable hiding (mapM, sequence)
import Data.List hiding (sort)
import qualified Data.List as List

import Agda.Syntax.Abstract.Views (isSet)
import Agda.Syntax.Literal
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.MetaVars.Occurs (killArgs,PruneResult(..))
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Free
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Level
import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Eliminators
-- import Agda.TypeChecking.UniversePolymorphism

import Agda.Utils.Size
import Agda.Utils.Monad
import Agda.Utils.Maybe

import Agda.TypeChecking.Monad.Debug

#include "../undefined.h"
import Agda.Utils.Impossible

mlevel :: TCM (Maybe Term)
mlevel = liftTCM $ (Just <$> primLevel) `catchError` \_ -> return Nothing

-- | Check if to lists of arguments are the same (and all variables).
--   Precondition: the lists have the same length.
sameVars :: Args -> Args -> Bool
sameVars xs ys = and $ zipWith same xs ys
    where
	same (Arg _ (Var n [])) (Arg _ (Var m [])) = n == m
        same _ _                                   = False

-- | @intersectVars us vs@ checks whether all relevant elements in @us@ and @vs@
--   are variables, and if yes, returns a prune list which says @True@ for
--   arguments which are different and can be pruned.
intersectVars :: Args -> Args -> Maybe [Bool]
intersectVars = zipWithM areVars where
    -- ignore irrelevant args
    areVars u v | isArgInfoIrrelevant (argInfo u) = Just False -- do not prune
    areVars (Arg _ (Var n [])) (Arg _ (Var m [])) = Just $ n /= m -- prune different vars
    areVars _ _                                   = Nothing

equalTerm :: Type -> Term -> Term -> TCM ()
equalTerm = compareTerm CmpEq

equalAtom :: Type -> Term -> Term -> TCM ()
equalAtom = compareAtom CmpEq

equalType :: Type -> Type -> TCM ()
equalType = compareType CmpEq

{- Comparing in irrelevant context always succeeds.

   However, we might want to dig for solutions of irrelevant metas.

   To this end, we can just ignore errors during conversion checking.
 -}

-- convError ::  MonadTCM tcm => TypeError -> tcm a
-- | Ignore errors in irrelevant context.
convError :: TypeError -> TCM ()
convError err = ifM ((==) Irrelevant <$> asks envRelevance) (return ()) $ typeError err

-- | Type directed equality on values.
--
compareTerm :: Comparison -> Type -> Term -> Term -> TCM ()
  -- If one term is a meta, try to instantiate right away. This avoids unnecessary unfolding.
  -- Andreas, 2012-02-14: This is UNSOUND for subtyping!
compareTerm cmp a u v = do
  -- Check syntactic equality first. This actually saves us quite a bit of work.
  (u, v) <- instantiateFull (u, v)
  if u == v then unifyPointers cmp u v $ verboseS "profile.sharing" 20 $ tick "equal terms" else do
  verboseS "profile.sharing" 20 $ tick "unequal terms"
  let checkPointerEquality def | not $ null $ List.intersect (pointerChain u) (pointerChain v) = do
        verboseS "profile.sharing" 10 $ tick "pointer equality"
        return ()
      checkPointerEquality def = def
  checkPointerEquality $ do
  reportSDoc "tc.conv.term" 10 $ sep [ text "compareTerm"
                                     , nest 2 $ prettyTCM u <+> prettyTCM cmp <+> prettyTCM v
                                     , nest 2 $ text ":" <+> prettyTCM a ]
  let fallback = compareTerm' cmp a u v
      unlessSubtyping cont =
          if cmp == CmpEq then cont else do
            -- do not short circuit size comparison!
            isSize <- isJust <$> do isSizeTypeTest <*> reduce a
            if isSize then fallback else cont
  case (ignoreSharing u, ignoreSharing v) of
    (MetaV x us, MetaV y vs)
      | x /= y    -> unlessSubtyping $ solve1 `orelse` solve2 `orelse` compareTerm' cmp a u v
      | otherwise -> fallback
      where
        (solve1, solve2) | x > y     = (assign x us v, assign y vs u)
                         | otherwise = (assign y vs u, assign x us v)
    (MetaV x us, _) -> unlessSubtyping $ assign x us v `orelse` fallback
    (_, MetaV y vs) -> unlessSubtyping $ assign y vs u `orelse` fallback
    _               -> fallback
  where
    assign x us v = do
      reportSDoc "tc.conv.term.shortcut" 20 $ sep
        [ text "attempting shortcut"
        , nest 2 $ prettyTCM (MetaV x us) <+> text ":=" <+> prettyTCM v
        ]
      ifM (isInstantiatedMeta x) patternViolation (assignV x us v)
      instantiate u
      -- () <- seq u' $ return ()
      reportSLn "tc.conv.term.shortcut" 50 $
        "shortcut successful\n  result: " ++ show u
    -- Should be ok with catchError_ but catchError is much safer since we don't
    -- rethrow errors.
    m `orelse` h = m `catchError` \err -> case err of
                    PatternErr s -> put s >> h
                    _            -> h

unifyPointers _ _ _ action = action
-- unifyPointers cmp _ _ action | cmp /= CmpEq = action
-- unifyPointers _ u v action = do
--   old <- gets stDirty
--   modify $ \s -> s { stDirty = False }
--   action
--   (u, v) <- instantiate (u, v)
--   dirty <- gets stDirty
--   modify $ \s -> s { stDirty = old }
--   when (not dirty) $ forceEqualTerms u v

compareTerm' :: Comparison -> Type -> Term -> Term -> TCM ()
compareTerm' cmp a m n =
  verboseBracket "tc.conv.term" 20 "compareTerm" $ do
  a' <- reduce a
  catchConstraint (ValueCmp cmp a' m n) $ do
    reportSDoc "tc.conv.term" 30 $ fsep
      [ text "compareTerm", prettyTCM m, prettyTCM cmp, prettyTCM n, text ":", prettyTCM a' ]
    proofIrr <- proofIrrelevance
    isSize   <- isJust <$> isSizeType a'
    s        <- reduce $ getSort a'
    mlvl     <- mlevel
    case s of
      Prop | proofIrr -> return ()
      _    | isSize   -> compareSizes cmp m n
      _               -> case ignoreSharing $ unEl a' of
        a | Just a == mlvl -> do
          a <- levelView m
          b <- levelView n
          equalLevel a b
-- OLD:        Pi dom _  -> equalFun (dom, a') m n
        a@Pi{}    -> equalFun a m n
        Lam _ _   -> __IMPOSSIBLE__
        Def r ps  -> do
          isrec <- isEtaRecord r
          if isrec
            then do
              m <- reduceB m
              n <- reduceB n
              case (m, n) of
                _ | isMeta m || isMeta n ->
                    compareAtom cmp a' (ignoreBlocking m) (ignoreBlocking n)

                _ | isNeutral m && isNeutral n -> do
                    -- Andreas 2011-03-23: (fixing issue 396)
                    -- if we are dealing with a singleton record,
                    -- we can succeed immediately
                    isSing <- isSingletonRecordModuloRelevance r ps
                    case isSing of
                      Right True -> return ()
                      -- do not eta-expand if comparing two neutrals
                      _ -> compareAtom cmp a' (ignoreBlocking m) (ignoreBlocking n)
                _ -> do
                  (tel, m') <- etaExpandRecord r ps $ ignoreBlocking m
                  (_  , n') <- etaExpandRecord r ps $ ignoreBlocking n
                  -- No subtyping on record terms
                  c <- getRecordConstructor r
                  compareArgs [] (telePi_ tel $ sort Prop) (Con c []) m' n'

            else compareAtom cmp a' m n
        _ -> compareAtom cmp a' m n
  where
-- Andreas, 2010-10-11: allowing neutrals to be blocked things does not seem
-- to change Agda's behavior
--    isNeutral Blocked{}          = False
    isNeutral = isNeutral' . fmap ignoreSharing
    isMeta    = isMeta'    . fmap ignoreSharing
    isNeutral' (NotBlocked Con{}) = False
    isNeutral' _                  = True
    isMeta' (NotBlocked MetaV{})  = True
    isMeta' _                     = False

    -- equality at function type (accounts for eta)
    equalFun :: Term -> Term -> Term -> TCM ()
    equalFun (Shared p) m n = equalFun (derefPtr p) m n
    equalFun (Pi dom@(Dom info _) b) m n = do
        name <- freshName_ $ properName $ absName b
        addCtx name dom $ compareTerm cmp (absBody b) m' n'
      where
        (m',n') = raise 1 (m,n) `apply` [Arg info $ var 0]
        properName "_" = "x"
        properName  x  =  x
    equalFun _ _ _ = __IMPOSSIBLE__
{- OLD CODE
    equalFun :: (Dom Type, Type) -> Term -> Term -> TCM ()
    equalFun (a@(Dom h r _), t) m n = do
        name <- freshName_ (suggest $ unEl t)
        addCtx name a $ compareTerm cmp t' m' n'
      where
        p	= Arg h r $ var 0
        (m',n') = raise 1 (m,n) `apply` [p]
        t'	= raise 1 t `piApply` [p]
        suggest (Pi _ b) = absName b
        suggest _	 = __IMPOSSIBLE__
-}

-- | @compareTel t1 t2 cmp tel1 tel1@ checks whether pointwise
--   @tel1 \`cmp\` tel2@ and complains that @t2 \`cmp\` t1@ failed if
--   not.
compareTel :: Type -> Type ->
  Comparison -> Telescope -> Telescope -> TCM ()
compareTel t1 t2 cmp tel1 tel2 =
  verboseBracket "tc.conv.tel" 20 "compareTel" $
  catchConstraint (TelCmp t1 t2 cmp tel1 tel2) $ case (tel1, tel2) of
    (EmptyTel, EmptyTel) -> return ()
    (EmptyTel, _)        -> bad
    (_, EmptyTel)        -> bad
    (ExtendTel arg1@(Dom i1 a1) tel1, ExtendTel arg2@(Dom i2 a2) tel2)
      | argInfoHiding i1 /= argInfoHiding i2 -> bad
        -- Andreas, 2011-09-11 do not test r1 == r2 because they could differ
        -- e.g. one could be Forced and the other Relevant (see fail/UncurryMeta)
      | otherwise -> do
          name <- freshName_ (suggest (absName tel1) (absName tel2))
          let checkArg = escapeContext 1 $ compareType cmp a1 a2
{- OLD
          let (tel1', tel2') = raise 1 (tel1, tel2)
              arg            = var 0
              c = TelCmp t1 t2 cmp (absApp tel1' arg) (absApp tel2' arg)
-}
              c = TelCmp t1 t2 cmp (absBody tel1) (absBody tel2)
              r = max (argInfoRelevance i1) (argInfoRelevance i2) -- take "most irrelevant"
              dependent = (r /= Irrelevant) && isBinderUsed tel2
          addCtx name arg1 $
            if dependent
	    then guardConstraint c checkArg
	    else checkArg >> solveConstraint_ c
          where
            suggest "_" y = y
            suggest  x  _ = x
  where
    -- Andreas, 2011-05-10 better report message about types
    bad = typeError $ UnequalTypes cmp t2 t1 -- switch t2 and t1 because of contravariance!
--    bad = typeError $ UnequalTelescopes cmp tel1 tel2

-- | Syntax directed equality on atomic values
--
compareAtom :: Comparison -> Type -> Term -> Term -> TCM ()
compareAtom cmp t m n =
    verboseBracket "tc.conv.atom" 20 "compareAtom" $
    -- if a PatternErr is thrown, rebuild constraint!
    catchConstraint (ValueCmp cmp t m n) $ do
      reportSDoc "tc.conv.atom" 50 $
	text "compareAtom" <+> fsep [ prettyTCM m <+> prettyTCM cmp
                                    , prettyTCM n
                                    , text ":" <+> prettyTCM t ]
      -- Andreas: what happens if I cut out the eta expansion here?
      -- Answer: Triggers issue 245, does not resolve 348
      mb' <- etaExpandBlocked =<< reduceB m
      nb' <- etaExpandBlocked =<< reduceB n

      -- constructorForm changes literal to constructors
      -- only needed if the other side is not a literal
      (mb'', nb'') <- case (ignoreSharing $ ignoreBlocking mb', ignoreSharing $ ignoreBlocking nb') of
	(Lit _, Lit _) -> return (mb', nb')
        _ -> (,) <$> traverse constructorForm mb'
                 <*> traverse constructorForm nb'

      mb <- traverse unLevel mb''
      nb <- traverse unLevel nb''

      let m = ignoreBlocking mb
          n = ignoreBlocking nb

          postpone = addConstraint $ ValueCmp cmp t m n

          checkSyntacticEquality = do
            n <- normalise n    -- is this what we want?
            m <- normalise m
            if m == n
                then return ()	-- Check syntactic equality for blocked terms
                else postpone

      unifyPointers cmp (ignoreBlocking mb') (ignoreBlocking nb') $ do    -- this needs to go after eta expansion to avoid creating infinite terms

      reportSDoc "tc.conv.atom" 30 $
	text "compareAtom" <+> fsep [ prettyTCM mb <+> prettyTCM cmp
                                    , prettyTCM nb
                                    , text ":" <+> prettyTCM t ]
      case (ignoreSharing <$> mb, ignoreSharing <$> nb) of
        -- equate two metas x and y.  if y is the younger meta,
        -- try first y := x and then x := y
        (NotBlocked (MetaV x xArgs), NotBlocked (MetaV y yArgs))
            | x == y ->
              case intersectVars xArgs yArgs of
                -- all relevant arguments are variables
                Just kills -> do
                  -- kills is a list with 'True' for each different var
                  killResult <- killArgs kills x
                  case killResult of
                    NothingToPrune   -> return ()
                    PrunedEverything -> return ()
                    PrunedNothing    -> postpone
                    PrunedSomething  -> postpone
                    -- OLD CODE: if killedAll then return () else checkSyntacticEquality
                -- not all relevant arguments are variables
                Nothing -> checkSyntacticEquality -- Check syntactic equality on meta-variables
                                -- (same as for blocked terms)
            | otherwise -> do
                [p1, p2] <- mapM getMetaPriority [x,y]
                -- instantiate later meta variables first
                let (solve1, solve2)
                      | (p1,x) > (p2,y) = (l,r)
                      | otherwise	    = (r,l)
                      where l = assignV x xArgs n
                            r = assignV y yArgs m

                    try m h = m `catchError_` \err -> case err of
                      PatternErr s -> put s >> h
                      _            -> throwError err

                -- First try the one with the highest priority. If that doesn't
                -- work, try the low priority one.
                try solve1 solve2

        -- one side a meta, the other an unblocked term
	(NotBlocked (MetaV x xArgs), _) -> assignV x xArgs n
	(_, NotBlocked (MetaV x xArgs)) -> assignV x xArgs m

        (Blocked{}, Blocked{})	-> checkSyntacticEquality
        (Blocked{}, _)    -> useInjectivity cmp t m n
        (_,Blocked{})     -> useInjectivity cmp t m n
        _ -> case (ignoreSharing m, ignoreSharing n) of
	    (Pi{}, Pi{}) -> equalFun m n

	    (Sort s1, Sort s2) -> compareSort CmpEq s1 s2

	    (Lit l1, Lit l2) | l1 == l2 -> return ()
	    (Var i iArgs, Var j jArgs) | i == j -> do
		a <- typeOfBV i
                -- Variables are invariant in their arguments
		compareArgs [] a (Var i []) iArgs jArgs
            (Def{}, Def{}) -> do
              ev1 <- elimView m
              ev2 <- elimView n
              reportSDoc "tc.conv.atom" 50 $
                sep [ text $ "ev1 = " ++ show ev1
                    , text $ "ev2 = " ++ show ev2 ]
              case (ev1, ev2) of
                (VarElim x els1, VarElim y els2) | x == y -> cmpElim (typeOfBV x) (Var x []) els1 els2
                (ConElim x els1, ConElim y els2) | x == y ->
                  cmpElim (conType x t) (Con x []) els1 els2
                  -- Andreas 2012-01-17 careful!  In the presence of
                  -- projection eliminations, t is NOT the datatype x belongs to
                  -- Ulf 2012-07-12: actually projection likeness is carefully
                  -- set up so that there can't be any projections from
                  -- constructor applications at this point, so t really is the
                  -- datatype of x. See issue 676 for an example where it
                  -- failed.
                (DefElim x els1, DefElim y els2) | x == y ->
                  cmpElim (defType <$> getConstInfo x) (Def x []) els1 els2
                (DefElim x els1, DefElim y els2) ->
                  trySizeUniv cmp t m n x els1 y els2
                (MetaElim{}, _) -> __IMPOSSIBLE__   -- projections from metas should have been eta expanded
                (_, MetaElim{}) -> __IMPOSSIBLE__
                _ -> typeError $ UnequalTerms cmp m n t
                where
                  polarities (Def x _) = getPolarity' cmp x
                  polarities _         = return []
                  cmpElim t v els1 els2 = do
                    a   <- t
                    pol <- polarities v
                    reportSDoc "tc.conv.elim" 10 $
                      text "compareElim" <+> vcat
                        [ text "pol  =" <+> text (show pol)
                        , text "a    =" <+> prettyTCM a
                        , text "v    =" <+> prettyTCM v
                        , text "els1 =" <+> prettyTCM els1
                        , text "els2 =" <+> prettyTCM els2
                        ]
                    compareElims pol a v els1 els2
	    (Con x xArgs, Con y yArgs)
		| x == y -> do
                    -- Get the type of the constructor instantiated to the datatype parameters.
                    a' <- conType x t
                    -- Constructors are invariant in their arguments
                    -- (could be covariant).
                    compareArgs [] a' (Con x []) xArgs yArgs
            _ -> typeError $ UnequalTerms cmp m n t
    where
        conType c (El _ v) = case ignoreSharing v of
          Def d args -> do
            npars <- do
              def <- theDef <$> getConstInfo d
              return $ case def of Datatype{dataPars = n} -> n
                                   Record{recPars = n}    -> n
                                   _                      -> __IMPOSSIBLE__
            a <- defType <$> getConstInfo c
            return $ piApply a (genericTake npars args)
          _ -> __IMPOSSIBLE__

        equalFun t1 t2 = case (ignoreSharing t1, ignoreSharing t2) of
	  (Pi dom1@(Dom i1 a1) b1, Pi (Dom i2 a2) b2)
	    | argInfoHiding i1 /= argInfoHiding i2 -> typeError $ UnequalHiding t1 t2
            -- Andreas 2010-09-21 compare r1 and r2, but ignore forcing annotations!
	    | not (compareRelevance cmp (ignoreForced $ argInfoRelevance i2)
                                        (ignoreForced $ argInfoRelevance i1))
                -> typeError $ UnequalRelevance cmp t1 t2
	    | otherwise -> verboseBracket "tc.conv.fun" 15 "compare function types" $ do
                reportSDoc "tc.conv.fun" 20 $ nest 2 $ vcat
                  [ text "t1 =" <+> prettyTCM t1
                  , text "t2 =" <+> prettyTCM t2 ]
                let checkDom = escapeContext 1 $ compareType cmp a2 a1
                    conCoDom = TypeCmp cmp (absBody b1) (absBody b2)
                -- We only need to require a1 == a2 if t2 is a dependent function type.
                -- If it's non-dependent it doesn't matter what we add to the context.
                name <- freshName_ (suggest b1 b2)
                addCtx name dom1 $
                  if isBinderUsed b2 -- dependent function type?
                  then guardConstraint conCoDom checkDom
                  else checkDom >> solveConstraint_ conCoDom
	    where
		suggest b1 b2 = head $
                  [ x | x <- map absName [b1,b2], x /= "_"] ++ ["_"]
	  _ -> __IMPOSSIBLE__

compareRelevance :: Comparison -> Relevance -> Relevance -> Bool
compareRelevance CmpEq  = (==)
compareRelevance CmpLeq = (<=)

-- | Type-directed equality on eliminator spines
compareElims :: [Polarity] -> Type -> Term -> [Elim] -> [Elim] -> TCM ()
compareElims _ _ _ [] [] = return ()
compareElims _ _ _ [] (_:_) = __IMPOSSIBLE__
compareElims _ _ _ (_:_) [] = __IMPOSSIBLE__
compareElims _ _ _ (Apply{} : _) (Proj{} : _) = __IMPOSSIBLE__
compareElims _ _ _ (Proj{} : _) (Apply{} : _) = __IMPOSSIBLE__
compareElims pols0 a v els01@(Apply arg1 : els1) els02@(Apply arg2 : els2) =
  verboseBracket "tc.conv.elim" 20 "compare Apply" $ do
  reportSDoc "tc.conv.elim" 25 $ nest 2 $ vcat
    [ text "a    =" <+> prettyTCM a
    , text "v    =" <+> prettyTCM v
    , text "arg1 =" <+> prettyTCM arg1
    , text "arg2 =" <+> prettyTCM arg2
    ]
  reportSDoc "tc.conv.elim" 10 $ nest 2 $ vcat
    [ text "v    =" <+> text (show v)
    , text "arg1 =" <+> text (show arg1)
    , text "arg2 =" <+> text (show arg2)
    , text ""
    ]
  let (pol, pols) = nextPolarity pols0
  ab <- reduceB a
  let a = ignoreBlocking ab
  catchConstraint (ElimCmp pols0 a v els01 els02) $ do
  reportSDoc "tc.conv.elim" 10 $ nest 2 $ vcat
    [ text "ab = " <+> text (show ab)
    , text "x = " <+> text (show (ignoreSharing . unEl <$> ab))
    ]
  case ignoreSharing . unEl <$> ab of
    Blocked{}                     -> patternViolation
    NotBlocked MetaV{}            -> patternViolation
    NotBlocked (Pi (Dom info b) _) -> do
      mlvl <- mlevel
      let checkArg = applyRelevanceToContext (argInfoRelevance info) $
                         case argInfoRelevance info of
            Forced     -> return ()
            r | irrelevantOrUnused r ->
                          compareIrrelevant b (unArg arg1) (unArg arg2)
            _          -> compareWithPol pol (flip compareTerm b)
                            (unArg arg1) (unArg arg2)
          dependent = case ignoreSharing $ unEl a of
            Pi (Dom _ (El _ lvl')) c -> 0 `freeInIgnoringSorts` absBody c
                                          && Just lvl' /= mlvl
            _ -> False

          theRest = ElimCmp pols (piApply a [arg1]) (apply v [arg1]) els1 els2

      if dependent
        then guardConstraint theRest checkArg
        else checkArg >> solveConstraint_ theRest

    NotBlocked (Def info _) -> do
                       reportSDoc "tc.conv.elim" 10 $ text "crash!"
                       __IMPOSSIBLE__
    NotBlocked a -> do reportSDoc "tc.conv.elim" 50 $ text (show a)
                       __IMPOSSIBLE__
--    _ -> __IMPOSSIBLE__
compareElims pols a v els01@(Proj f : els1) els02@(Proj f' : els2)
  | f /= f'   = typeError . GenericError . show =<< prettyTCM f <+> text "/=" <+> prettyTCM f'
  | otherwise = do
    a <- reduce a
    case ignoreSharing $ unEl a of
      Def r us -> do
        let (pol, _) = nextPolarity pols
        ft <- defType <$> getConstInfo f  -- get type of projection function
        let arg = defaultArg v  -- TODO: not necessarily relevant?
        let c = piApply ft (us ++ [arg])
        (cmp, els1, els2) <- return $ case pol of
              Invariant     -> (CmpEq, els1, els2)
              Covariant     -> (CmpLeq, els1, els2)
              Contravariant -> (CmpLeq, els2, els1)
              Nonvariant    -> __IMPOSSIBLE__ -- the polarity should be Invariant
        pols' <- getPolarity' cmp f
        compareElims pols' c (Def f [arg]) els1 els2
      _ -> __IMPOSSIBLE__

-- | "Compare" two terms in irrelevant position.  This always succeeds.
--   However, we can dig for solutions of irrelevant metas in the
--   terms we compare.
--   (Certainly not the systematic solution, that'd be proof search...)
compareIrrelevant :: Type -> Term -> Term -> TCM ()
{- 2012-04-02 DontCare no longer present
compareIrrelevant a (DontCare v) w = compareIrrelevant a v w
compareIrrelevant a v (DontCare w) = compareIrrelevant a v w
-}
compareIrrelevant a v w = do
  reportSDoc "tc.conv.irr" 20 $ vcat
    [ text "compareIrrelevant"
    , nest 2 $ text "v =" <+> prettyTCM v
    , nest 2 $ text "w =" <+> prettyTCM w
    ]
  reportSDoc "tc.conv.irr" 50 $ vcat
    [ nest 2 $ text $ "v = " ++ show v
    , nest 2 $ text $ "w = " ++ show w
    ]
  try v w $ try w v $ return ()
  where
    try (Shared p) w fallback = try (derefPtr p) w fallback
    try (MetaV x vs) w fallback = do
      mv <- lookupMeta x
      let rel  = getMetaRelevance mv
          inst = case mvInstantiation mv of
                   InstV{} -> True
                   InstS{} -> True
                   _       -> False
      reportSDoc "tc.conv.irr" 20 $ vcat
        [ nest 2 $ text $ "rel  = " ++ show rel
        , nest 2 $ text $ "inst = " ++ show inst
        ]
      if not (irrelevantOrUnused rel) || inst then fallback else assignV x vs w
        -- the value of irrelevant or unused meta does not matter
    try v w fallback = fallback

compareWithPol :: Polarity -> (Comparison -> a -> a -> TCM ()) -> a -> a -> TCM ()
compareWithPol Invariant     cmp x y = cmp CmpEq x y
compareWithPol Covariant     cmp x y = cmp CmpLeq x y
compareWithPol Contravariant cmp x y = cmp CmpLeq y x
compareWithPol Nonvariant    cmp x y = return ()

-- | Type-directed equality on argument lists
--
compareArgs :: [Polarity] -> Type -> Term -> Args -> Args -> TCM ()
compareArgs pol a v args1 args2 =
  compareElims pol a v (map Apply args1) (map Apply args2)

---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | Equality on Types
compareType :: Comparison -> Type -> Type -> TCM ()
compareType cmp ty1@(El s1 a1) ty2@(El s2 a2) =
    verboseBracket "tc.conv.type" 20 "compareType" $
    catchConstraint (TypeCmp cmp ty1 ty2) $ do
	reportSDoc "tc.conv.type" 50 $ vcat
          [ text "compareType" <+> sep [ prettyTCM ty1 <+> prettyTCM cmp
                                       , prettyTCM ty2 ]
          , hsep [ text "   sorts:", prettyTCM s1, text " and ", prettyTCM s2 ]
          ]
-- Andreas, 2011-4-27 should not compare sorts, but currently this is needed
-- for solving sort and level metas
	compareSort CmpEq s1 s2 `catchError` \err -> case err of
          TypeError _ e -> do
            reportSDoc "tc.conv.type" 30 $ vcat
              [ text "sort comparison failed"
              , nest 2 $ vcat
                [ text "s1 =" <+> prettyTCM s1
                , text "s2 =" <+> prettyTCM s2
                ]
              ]
            case clValue e of
              -- Issue 659: Better error message
              SetOmegaNotValidType -> typeError $ UnequalBecauseOfUniverseConflict cmp a1 a2
              _ -> do
                -- This error will probably be more informative
                compareTerm cmp (sort s1) a1 a2
                -- Throw the original error if the above doesn't
                -- give an error (for instance, due to pending
                -- constraints).
                -- Or just ignore it... We run into this with irrelevant levels
                -- which may show up in sort constraints, causing them to fail.
                -- In any case it's not safe to ignore the error, for instance
                -- a1 might be Set and a2 a meta of type Set, in which case we
                -- really need the sort comparison to fail, instead of silently
                -- instantiating the meta.
                throwError err
          _             -> throwError err
	compareTerm cmp (sort s1) a1 a2
	return ()

leqType :: Type -> Type -> TCM ()
leqType = compareType CmpLeq

-- | @coerce v a b@ coerces @v : a@ to type @b@, returning a @v' : b@
--   with maybe extra hidden applications or hidden abstractions.
--
--   In principle, this function can host coercive subtyping, but
--   currently it only tries to fix problems with hidden function types.
coerce :: Term -> Type -> Type -> TCM Term
coerce v t1 t2 = blockTerm t2 $ do
  verboseS "tc.conv.coerce" 10 $ do
    (a1,a2) <- reify (t1,t2)
    let dbglvl = if isSet a1 && isSet a2 then 50 else 10
    reportSDoc "tc.conv.coerce" dbglvl $
      text "coerce" <+> vcat
        [ text "term      v  =" <+> prettyTCM v
        , text "from type t1 =" <+> prettyTCM a1
        , text "to type   t2 =" <+> prettyTCM a2
        ]
  -- v <$ do workOnTypes $ leqType t1 t2
  -- take off hidden/instance domains from t1 and t2
  TelV tel1 b1 <- telViewUpTo' (-1) ((NotHidden /=) . domHiding) t1
  TelV tel2 b2 <- telViewUpTo' (-1) ((NotHidden /=) . domHiding) t2
  let n = size tel1 - size tel2
  -- the crude solution would be
  --   v' = λ {tel2} → v {tel1}
  -- however, that may introduce unneccessary many function types
  -- If n  > 0 and b2 is not blocked, it is safe to
  -- insert n many hidden args
  if n <= 0 then fallback else do
    ifBlockedType b2 (\ _ _ -> fallback) $ \ _ -> do
      (args, t1') <- implicitArgs n (NotHidden /=) t1
      v `apply` args <$ do workOnTypes $ leqType t1' t2
  where
    fallback = v <$ do workOnTypes $ leqType t1 t2

---------------------------------------------------------------------------
-- * Sorts
---------------------------------------------------------------------------

compareSort :: Comparison -> Sort -> Sort -> TCM ()
compareSort CmpEq  = equalSort
compareSort CmpLeq = equalSort

-- | Check that the first sort is less or equal to the second.
leqSort :: Sort -> Sort -> TCM ()
leqSort s1 s2 =
  ifM typeInType (return ()) $
    catchConstraint (SortCmp CmpLeq s1 s2) $
    do	(s1,s2) <- reduce (s1,s2)
        reportSDoc "tc.conv.sort" 30 $
          sep [ text "leqSort"
              , nest 2 $ fsep [ prettyTCM s1 <+> text "=<"
                              , prettyTCM s2 ]
              ]
	case (s1, s2) of

            (Type a, Type b) -> leqLevel a b

	    (Prop    , Prop    )	     -> return ()
	    (Type _  , Prop    )	     -> notLeq s1 s2

	    (Prop    , Type _  )	     -> return ()

            (_       , Inf     )             -> return ()
            (Inf     , _       )             -> equalSort s1 s2
            (DLub{}  , _       )             -> equalSort s1 s2
            (_       , DLub{}  )             -> equalSort s1 s2
    where
	notLeq s1 s2 = typeError $ NotLeqSort s1 s2

leqLevel :: Level -> Level -> TCM ()
leqLevel a b = liftTCM $ do
  reportSDoc "tc.conv.nat" 30 $
    text "compareLevel" <+>
      sep [ prettyTCM a <+> text "=<"
          , prettyTCM b ]
  a <- reduce a
  b <- reduce b
  catchConstraint (LevelCmp CmpLeq a b) $ leqView a b
  where
    leqView a@(Max as) b@(Max bs) = do
      reportSDoc "tc.conv.nat" 30 $
        text "compareLevelView" <+>
          sep [ text (show a) <+> text "=<"
              , text (show b) ]
      wrap $ case (as, bs) of

        -- same term
        _ | as == bs -> ok

        -- 0 ≤ any
        ([], _) -> ok

        -- as ≤ 0
        (as, [])  -> sequence_ [ equalLevel (Max [a]) (Max []) | a <- as ]

        -- as ≤ [b]
        (as@(_:_:_), [b]) -> sequence_ [ leqView (Max [a]) (Max [b]) | a <- as ]

        -- reduce constants
        (as, bs) | minN > 0 -> leqView (Max $ map (subtr minN) as) (Max $ map (subtr minN) bs)
          where
            ns = map constant as
            ms = map constant bs
            minN = minimum (ns ++ ms)

        -- remove subsumed
        (as, bs)
          | not $ null dups -> leqView (Max $ as \\ dups) (Max bs)
          where
            dups = [ a | a@(Plus m l) <- as, Just n <- [findN l], m <= n ]
            findN a = case [ n | Plus n b <- bs, b == a ] of
                        [n] -> Just n
                        _   -> Nothing

        -- Andreas, 2012-10-02 raise error on unsolvable constraint
        ([ClosedLevel n], [ClosedLevel m]) -> if n <= m then ok else notok

        -- closed ≤ bs
        ([ClosedLevel n], bs)
          | n <= maximum (map constant bs) -> ok

        -- as ≤ neutral
        (as, bs)
          | neutralB && maxA > maxB -> notok
          | neutralB && any (\a -> neutral a && not (isInB a)) as -> notok
          | neutralB && neutralA -> maybeok $ all (\a -> constant a <= findN a) as
          where
            maxA = maximum $ map constant as
            maxB = maximum $ map constant bs
            neutralA = all neutral as
            neutralB = all neutral bs
            isInB a = elem (unneutral a) $ map unneutral bs
            findN a = case [ n | b@(Plus n _) <- bs, unneutral b == unneutral a ] of
                        [n] -> n
                        _   -> __IMPOSSIBLE__

        -- [a] ≤ [neutral]
        ([a@(Plus n _)], [b@(Plus m NeutralLevel{})])
          | m == n -> equalLevel (Max [a]) (Max [b])

        -- anything else
        _ -> postpone
      where
        ok       = return ()
        notok    = typeError $ NotLeqSort (Type a) (Type b)
        postpone = patternViolation

        wrap m = catchError m $ \e ->
          case e of
            TypeError{} -> notok
            _           -> throwError e

        maybeok True = ok
        maybeok False = notok

        neutral (Plus _ NeutralLevel{}) = True
        neutral _                       = False

        meta (Plus _ MetaLevel{}) = True
        meta _                    = False

        unneutral (Plus _ (NeutralLevel v)) = v
        unneutral _ = __IMPOSSIBLE__

        constant (ClosedLevel n) = n
        constant (Plus n _)      = n

        subtr m (ClosedLevel n) = ClosedLevel (n - m)
        subtr m (Plus n l)      = Plus (n - m) l

--     choice []     = patternViolation
--     choice (m:ms) = noConstraints m `catchError` \_ -> choice ms
--       case e of
--         PatternErr{} -> choice ms
--         _            -> throwError e

equalLevel :: Level -> Level -> TCM ()
equalLevel a b = do
  a <- reduce a
  b <- reduce b
  reportSLn "tc.conv.level" 50 $ "equalLevel (" ++ show a ++ ") (" ++ show b ++ ")"
  liftTCM $ catchConstraint (LevelCmp CmpEq a b) $
    check a b
  where
    check a@(Max as) b@(Max bs) = do
      reportSDoc "tc.conv.level" 40 $
        sep [ text "equalLevel"
            , vcat [ nest 2 $ sep [ prettyTCM a <+> text "=="
                                  , prettyTCM b
                                  ]
                   , nest 2 $ sep [ text (show (Max as)) <+> text "=="
                                  , text (show (Max bs))
                                  ]
                   ]
            ]
      let a === b   = do
            lvl <- getLvl
            equalAtom lvl a b
          as =!= bs = levelTm (Max as) === levelTm (Max bs)
      as <- return $ closed0 as
      bs <- return $ closed0 bs
      case (as, bs) of
        _ | List.sort as == List.sort bs -> ok
          | any isBlocked (as ++ bs) -> do
              lvl <- getLvl
              liftTCM $ useInjectivity CmpEq lvl (Level a) (Level b)

        -- closed == closed
        ([ClosedLevel n], [ClosedLevel m])
          | n == m    -> ok
          | otherwise -> notok

        -- closed == neutral
        ([ClosedLevel{}], _) | any isNeutral bs -> notok
        (_, [ClosedLevel{}]) | any isNeutral as -> notok

        -- 0 == any
        ([ClosedLevel 0], bs@(_:_:_)) -> sequence_ [ equalLevel (Max []) (Max [b]) | b <- bs ]
        (as@(_:_:_), [ClosedLevel 0]) -> sequence_ [ equalLevel (Max [a]) (Max []) | a <- as ]

        -- Same meta
        ([Plus n (MetaLevel x _)], [Plus m (MetaLevel y _)])
          | n == m && x == y -> ok

        -- meta == any
        ([Plus n (MetaLevel x as)], _)
          | any (isThisMeta x) bs -> postpone
        (_, [Plus n (MetaLevel x bs)])
          | any (isThisMeta x) as -> postpone
        ([Plus n (MetaLevel x as')], [Plus m (MetaLevel y bs')])
          | (n, y) < (m, x)            -> meta n x as' bs
          | otherwise                  -> meta m y bs' as
        ([Plus n (MetaLevel x as)], _) -> meta n x as bs
        (_, [Plus n (MetaLevel x bs)]) -> meta n x bs as

        -- any other metas
        _ | any isMeta (as ++ bs) -> postpone

        -- neutral/closed == neutral/closed
        _ | all isNeutralOrClosed (as ++ bs) ->
          if length as == length bs
            then zipWithM_ (\a b -> [a] =!= [b]) as bs
            else notok

        -- more cases?
        _ -> postpone

      where
        ok       = return ()
        notok    = typeError $ UnequalSorts (Type a) (Type b)
        postpone = do
          reportSLn "tc.conv.level" 30 $ "postponing: " ++ show a ++ " == " ++ show b
          patternViolation

        closed0 [] = [ClosedLevel 0]
        closed0 as = as

        getLvl = El (mkType 0) <$> primLevel

        meta n x as bs = do
          reportSLn "tc.meta.level" 50 $ "meta " ++ show as ++ " " ++ show bs
          bs' <- mapM (subtr n) bs
          assignV x as $ levelTm (Max bs')

        -- Make sure to give a sensible error message
        wrap m = m `catchError` \err ->
          case err of
            TypeError{} -> notok
            _           -> throwError err

        subtr n (ClosedLevel m)
          | m >= n    = return $ ClosedLevel (m - n)
          | otherwise = notok
        subtr n (Plus m a)
          | m >= n    = return $ Plus (m - n) a
        subtr _ (Plus _ BlockedLevel{}) = postpone
        subtr _ (Plus _ MetaLevel{})    = postpone
        subtr _ (Plus _ NeutralLevel{}) = postpone
        subtr _ (Plus _ UnreducedLevel{}) = __IMPOSSIBLE__

        isNeutral (Plus _ NeutralLevel{}) = True
        isNeutral _                       = False

        isClosed ClosedLevel{} = True
        isClosed _             = False

        isNeutralOrClosed l = isClosed l || isNeutral l

        isBlocked (Plus _ BlockedLevel{}) = True
        isBlocked _                     = False

        isMeta (Plus _ MetaLevel{}) = True
        isMeta _                  = False

        isThisMeta x (Plus _ (MetaLevel y _)) = x == y
        isThisMeta _ _                      = False


-- | Check that the first sort equal to the second.
equalSort :: Sort -> Sort -> TCM ()
equalSort s1 s2 =
  ifM typeInType (return ()) $
    catchConstraint (SortCmp CmpEq s1 s2) $ do
        (s1,s2) <- reduce (s1,s2)
        reportSDoc "tc.conv.sort" 30 $
          sep [ text "equalSort"
              , vcat [ nest 2 $ fsep [ prettyTCM s1 <+> text "=="
                                     , prettyTCM s2 ]
                     , nest 2 $ fsep [ text (show s1) <+> text "=="
                                     , text (show s2) ]
                     ]
              ]
	case (s1, s2) of

            (Type a  , Type b  ) -> equalLevel a b

	    (Prop    , Prop    ) -> return ()
	    (Type _  , Prop    ) -> notEq s1 s2
	    (Prop    , Type _  ) -> notEq s1 s2

            (Inf     , Inf     )             -> return ()
            (Inf     , Type (Max as@(_:_)))  -> mapM_ (isInf $ notEq s1 s2) as
            (Type (Max as@(_:_)), Inf)       -> mapM_ (isInf $ notEq s1 s2) as
            (Inf     , _       )             -> notEq s1 s2
            (_       , Inf     )             -> notEq s1 s2

            (DLub s1 s2, s0@(Type (Max []))) -> do
              equalSort s1 s0
              underAbstraction_ s2 $ \s2 -> equalSort s2 s0
            (s0@(Type (Max [])), DLub s1 s2) -> do
              equalSort s0 s1
              underAbstraction_ s2 $ \s2 -> equalSort s0 s2
            (DLub{}  , _       )             -> addConstraint (SortCmp CmpEq s1 s2)
            (_       , DLub{}  )             -> addConstraint (SortCmp CmpEq s1 s2)
    where
	notEq s1 s2 = typeError $ UnequalSorts s1 s2

        isInf notok ClosedLevel{} = notok
        isInf notok (Plus _ l) = case l of
          MetaLevel x vs          -> assignV x vs (Sort Inf)
          NeutralLevel (Shared p) -> isInf notok (Plus 0 $ NeutralLevel $ derefPtr p)
          NeutralLevel (Sort Inf) -> return ()
          _                       -> notok
