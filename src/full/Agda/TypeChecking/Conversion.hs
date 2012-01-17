{-# LANGUAGE CPP, PatternGuards #-}

module Agda.TypeChecking.Conversion where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Error
import Data.Traversable hiding (mapM, sequence)
import Data.List hiding (sort)
import qualified Data.List as List

import Agda.Syntax.Literal
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.MetaVars.Occurs (killArgs,PruneResult(..))
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Free
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Level
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Eliminators
-- import Agda.TypeChecking.UniversePolymorphism

import Agda.Utils.Monad

import Agda.TypeChecking.Monad.Debug

#include "../undefined.h"
import Agda.Utils.Impossible

mlevel :: TCM (Maybe Term)
mlevel = liftTCM $ (Just <$> primLevel) `catchError` \_ -> return Nothing

nextPolarity []       = (Invariant, [])
nextPolarity (p : ps) = (p, ps)

-- | Check if to lists of arguments are the same (and all variables).
--   Precondition: the lists have the same length.
sameVars :: Args -> Args -> Bool
sameVars xs ys = and $ zipWith same xs ys
    where
	same (Arg _ _ (Var n [])) (Arg _ _ (Var m [])) = n == m
	same _ _				       = False

-- | @intersectVars us vs@ checks whether all relevant elements in @us@ and @vs@
--   are variables, and if yes, returns a prune list which says @True@ for
--   arguments which are different and can be pruned.
intersectVars :: Args -> Args -> Maybe [Bool]
intersectVars = zipWithM areVars where
    -- ignore irrelevant args
    areVars u v | argRelevance u == Irrelevant        = Just False -- do not prune
    areVars (Arg _ _ (Var n [])) (Arg _ _ (Var m [])) = Just $ n /= m -- prune different vars
    areVars _ _                                       = Nothing

equalTerm :: Type -> Term -> Term -> TCM ()
equalTerm = compareTerm CmpEq

equalAtom :: Type -> Term -> Term -> TCM ()
equalAtom = compareAtom CmpEq

equalType :: Type -> Type -> TCM ()
equalType = compareType CmpEq

-- | Type directed equality on values.
--
compareTerm :: Comparison -> Type -> Term -> Term -> TCM ()
  -- If one term is a meta, try to instantiate right away. This avoids unnecessary unfolding.
compareTerm cmp a u v = liftTCM $ do
  (u, v) <- instantiate (u, v)
  reportSDoc "tc.conv.term" 10 $ sep [ text "compareTerm"
                                     , nest 2 $ prettyTCM u <+> prettyTCM cmp <+> prettyTCM v
                                     , nest 2 $ text ":" <+> prettyTCM a ]
  let fallback = compareTerm' cmp a u v
  case (u, v) of
    (u@(MetaV x us), v@(MetaV y vs))
      | x /= y    -> solve1 `orelse` solve2 `orelse` compareTerm' cmp a u v
      | otherwise -> fallback
      where
        (solve1, solve2) | x > y     = (assign x us v, assign y vs u)
                         | otherwise = (assign y vs u, assign x us v)
    (u@(MetaV x us), v) -> assign x us v `orelse` fallback
    (u, v@(MetaV y vs)) -> assign y vs u `orelse` fallback
    _                   -> fallback
  where
    assign x us v = do
      reportSDoc "tc.conv.term" 20 $ sep [ text "attempting shortcut"
                                         , nest 2 $ prettyTCM (MetaV x us) <+> text ":=" <+> prettyTCM v ]
      ifM (isInstantiatedMeta x) patternViolation (assignV x us v)
    -- Should be ok with catchError_ but catchError is much safer since we don't
    -- rethrow errors.
    m `orelse` h = m `catchError` \err -> case errError err of
                    PatternErr s -> put s >> h
                    _            -> h

compareTerm' :: Comparison -> Type -> Term -> Term -> TCM ()
compareTerm' cmp a m n =
  verboseBracket "tc.conv.term" 20 "compareTerm" $ do
  a' <- reduce a
  catchConstraint (ValueCmp cmp a' m n) $ do
    reportSDoc "tc.conv.term" 30 $ fsep
      [ text "compareTerm", prettyTCM m, prettyTCM cmp, prettyTCM n, text ":", prettyTCM a' ]
    proofIrr <- proofIrrelevance
    isSize   <- isSizeType a'
    s        <- reduce $ getSort a'
    mlvl     <- mlevel
    case s of
      Prop | proofIrr -> return ()
      _    | isSize   -> compareSizes cmp m n
      _               -> case unEl a' of
        a | Just a == mlvl -> do
          a <- levelView m
          b <- levelView n
          equalLevel a b
        Pi a _    -> equalFun (a,a') m n
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
    isNeutral (NotBlocked Con{}) = False
    isNeutral _                  = True
    isMeta (NotBlocked MetaV{})  = True
    isMeta _                     = False

    equalFun (a,t) m n = do
        name <- freshName_ (suggest $ unEl t)
        addCtx name a $ compareTerm cmp t' m' n'
      where
        p	= fmap (const $ Var 0 []) a
        (m',n') = raise 1 (m,n) `apply` [p]
        t'	= raise 1 t `piApply` [p]
        suggest (Pi _ b) = absName b
        suggest _	 = __IMPOSSIBLE__

-- | @compareTel t1 t2 cmp tel1 tel1@ checks whether pointwise @tel1 `cmp` tel2@
--   and complains that @t2 `cmp` t1@ failed if not.
compareTel :: Type -> Type ->
  Comparison -> Telescope -> Telescope -> TCM ()
compareTel t1 t2 cmp tel1 tel2 =
  verboseBracket "tc.conv.tel" 20 "compareTel" $
  catchConstraint (TelCmp t1 t2 cmp tel1 tel2) $ case (tel1, tel2) of
    (EmptyTel, EmptyTel) -> return ()
    (EmptyTel, _)        -> bad
    (_, EmptyTel)        -> bad
    (ExtendTel arg1@(Arg h1 r1 a1) tel1, ExtendTel arg2@(Arg h2 r2 a2) tel2)
      | h1 /= h2 -> bad
        -- Andreas, 2011-09-11 do not test r1 == r2 because they could differ
        -- e.g. one could be Forced and the other Relevant (see fail/UncurryMeta)
      | otherwise -> do
          let (tel1', tel2') = raise 1 (tel1, tel2)
              arg            = Var 0 []
          name <- freshName_ (suggest (absName tel1) (absName tel2))
          let checkArg = escapeContext 1 $ compareType cmp a1 a2
          let c = TelCmp t1 t2 cmp (absApp tel1' arg) (absApp tel2' arg)
          let r = max r1 r2  -- take "most irrelevant"
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
      let unLevel (Level l) = reallyUnLevelView l
          unLevel v = return v
      -- constructorForm changes literal to constructors
      -- Andreas: what happens if I cut out the eta expansion here?
      -- Answer: Triggers issue 245, does not resolve 348
      mb <- traverse unLevel =<< traverse constructorForm =<< etaExpandBlocked =<< reduceB m
      nb <- traverse unLevel =<< traverse constructorForm =<< etaExpandBlocked =<< reduceB n

      let m = ignoreBlocking mb
          n = ignoreBlocking nb

          postpone = addConstraint $ ValueCmp cmp t m n

          checkSyntacticEquality = do
            n <- normalise n    -- is this what we want?
            m <- normalise m
            if m == n
                then return ()	-- Check syntactic equality for blocked terms
                else postpone

      reportSDoc "tc.conv.atom" 30 $
	text "compareAtom" <+> fsep [ prettyTCM mb <+> prettyTCM cmp
                                    , prettyTCM nb
                                    , text ":" <+> prettyTCM t ]
      case (mb, nb) of
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

                    try m h = m `catchError_` \err -> case errError err of
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
        _ -> case (m, n) of
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
                (DefElim x els1, DefElim y els2) | x == y ->
                  cmpElim (defType <$> getConstInfo x) (Def x []) els1 els2
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
                        [ text "a    =" <+> prettyTCM a
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
        conType c (El _ (Def d args)) = do
          npars <- do
            def <- theDef <$> getConstInfo d
            return $ case def of Datatype{dataPars = n} -> n
                                 Record{recPars = n}    -> n
                                 _                      -> __IMPOSSIBLE__
          a <- defType <$> getConstInfo c
          return $ piApply a (genericTake npars args)
        conType _ _ = __IMPOSSIBLE__

	equalFun t1@(Pi arg1@(Arg h1 r1 a1) _) t2@(Pi (Arg h2 r2 a2) _)
	    | h1 /= h2	= typeError $ UnequalHiding ty1 ty2
            -- Andreas 2010-09-21 compare r1 and r2, but ignore forcing annotations!
	    | ignoreForced r1 /= ignoreForced r2 = typeError $ UnequalRelevance ty1 ty2
	    | otherwise = verboseBracket "tc.conv.fun" 15 "compare function types" $ do
                reportSDoc "tc.conv.fun" 20 $ nest 2 $ vcat
                  [ text "t1 =" <+> prettyTCM t1
                  , text "t2 =" <+> prettyTCM t2 ]
                let (ty1',ty2') = raise 1 (ty1,ty2)
                    arg	    = Arg h1 r1 (Var 0 [])
                name <- freshName_ (suggest t1 t2)
                let checkArg = escapeContext 1 $ compareType cmp a2 a1
                    c        = TypeCmp cmp (piApply ty1' [arg]) (piApply ty2' [arg])

                -- We only need to require a1 == a2 if t2 is a dependent function type.
                -- If it's non-dependent it doesn't matter what we add to the context.
                let dependent = case t2 of
                                    Pi _ b  -> isBinderUsed b
                                    _       -> __IMPOSSIBLE__
                addCtx name arg1 $
                  if dependent
                  then guardConstraint c checkArg
                  else checkArg >> solveConstraint_ c
	    where
		ty1 = El (getSort a1) t1    -- TODO: wrong (but it doesn't matter)
		ty2 = El (getSort a2) t2
		suggest t1 t2 = case concatMap name [t1,t2] of
				    []	-> "_"
				    x:_	-> x
		    where
			name (Pi _ b) = filter (/= "_") [absName b]
			name _        = __IMPOSSIBLE__
	equalFun _ _ = __IMPOSSIBLE__

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
    , text "els1 =" <+> prettyTCM els01
    , text "els2 =" <+> prettyTCM els02
    ]
  let (pol, pols) = nextPolarity pols0
  ab <- reduceB a
  let a = ignoreBlocking ab
  catchConstraint (ElimCmp pols0 a v els01 els02) $ do
  case unEl <$> ab of
    Blocked{}                     -> patternViolation
    NotBlocked MetaV{}            -> patternViolation
    NotBlocked (Pi (Arg _ r b) _) -> do
      let cmp x y = case pol of
                      Invariant     -> compareTerm CmpEq  b x y
                      Covariant     -> compareTerm CmpLeq b x y
                      Contravariant -> compareTerm CmpLeq b y x
      mlvl <- mlevel
      let checkArg = case r of
            Forced     -> return ()
            Irrelevant -> return () -- Andreas: ignore irr. func. args.
            _          -> applyRelevanceToContext r $
                            cmp (unArg arg1) (unArg arg2)
          dependent = case unEl a of
            Pi (Arg _ _ (El _ lvl')) c -> 0 `freeInIgnoringSorts` absBody c
                                          && Just lvl' /= mlvl
            _ -> False

          theRest = ElimCmp pols (piApply a [arg1]) (apply v [arg1]) els1 els2

      if dependent
        then guardConstraint theRest checkArg
        else checkArg >> solveConstraint_ theRest

    _ -> __IMPOSSIBLE__
compareElims pols a v els01@(Proj f : els1) els02@(Proj f' : els2)
  | f /= f'   = typeError . GenericError . show =<< prettyTCM f <+> text "/=" <+> prettyTCM f'
  | otherwise = do
    a <- reduce a
    case unEl a of
      Def r us -> do
        let (pol, _) = nextPolarity pols
        ft <- defType <$> getConstInfo f
        let arg = Arg NotHidden Relevant v  -- TODO: not necessarily relevant?
        let c = piApply ft (us ++ [arg])
        (cmp, els1, els2) <- return $ case pol of
              Invariant     -> (CmpEq, els1, els2)
              Covariant     -> (CmpLeq, els1, els2)
              Contravariant -> (CmpLeq, els2, els2)
        pols' <- getPolarity' cmp f
        compareElims pols' c (Def f [arg]) els1 els2
      _ -> __IMPOSSIBLE__

-- | Type-directed equality on argument lists
--
compareArgs :: [Polarity] -> Type -> Term -> Args -> Args -> TCM ()
compareArgs pol a v args1 args2 =
  compareElims pol a v (map Apply args1) (map Apply args2)

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
--        let cs1 = []
	compareSort CmpEq s1 s2 `catchError` \err -> case errError err of
                  TypeError _ _ -> do
                    reportSDoc "tc.conv.type" 30 $ vcat
                      [ text "sort comparison failed"
                      , nest 2 $ vcat
                        [ text "s1 =" <+> prettyTCM s1
                        , text "s2 =" <+> prettyTCM s2
                        ]
                      ]
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
	case (s1,s2) of

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
          case errError e of
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
--       case errError e of
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
        _ | all isNeutralOrClosed (as ++ bs) -> as =!= bs

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
          case errError err of
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
	case (s1,s2) of

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
          NeutralLevel (Sort Inf) -> return ()
          _                       -> notok
