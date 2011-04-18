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
import Agda.TypeChecking.MetaVars.Occurs (killArgs)
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
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.UniversePolymorphism

import Agda.Utils.Monad

import Agda.TypeChecking.Monad.Debug

#include "../undefined.h"
import Agda.Utils.Impossible

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

equalTerm :: MonadTCM tcm => Type -> Term -> Term -> tcm Constraints
equalTerm = compareTerm CmpEq

equalAtom :: MonadTCM tcm => Type -> Term -> Term -> tcm Constraints
equalAtom = compareAtom CmpEq

equalArgs :: MonadTCM tcm => Type -> Args -> Args -> tcm Constraints
equalArgs = compareArgs []

equalType :: MonadTCM tcm => Type -> Type -> tcm Constraints
equalType = compareType CmpEq

-- | Type directed equality on values.
--
compareTerm :: MonadTCM tcm => Comparison -> Type -> Term -> Term -> tcm Constraints
compareTerm cmp a m n =
  verboseBracket "tc.conv.term" 5 "compareTerm" $
  catchConstraint (ValueCmp cmp a m n) $ do
    a'       <- reduce a
    reportSDoc "tc.conv.term" 10 $ fsep
      [ text "compareTerm", prettyTCM m, prettyTCM cmp, prettyTCM n, text ":", prettyTCM a' ]
    proofIrr <- proofIrrelevance
    isSize   <- isSizeType a'
    s        <- reduce $ getSort a'
    mlvl     <- mlevel
    case s of
      Prop | proofIrr -> return []
      _    | isSize   -> compareSizes cmp m n
      _               -> case unEl a' of
        a | Just a == mlvl -> equalLevel m n
        Pi a _    -> equalFun (a,a') m n
        Fun a _   -> equalFun (a,a') m n
        MetaV x _ -> do
          (m,n) <- normalise (m,n)
          if m == n
            then return []
            else buildConstraint (ValueCmp cmp a m n)
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
                      Right True -> return []
                      -- do not eta-expand if comparing two neutrals
                      _ -> compareAtom cmp a' (ignoreBlocking m) (ignoreBlocking n)
                _ -> do
                  (tel, m') <- etaExpandRecord r ps $ ignoreBlocking m
                  (_  , n') <- etaExpandRecord r ps $ ignoreBlocking n
                  -- No subtyping on record terms
                  compareArgs [] (telePi_ tel $ sort Prop) m' n'

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
        suggest (Fun _ _)	 = "x"
        suggest (Pi _ (Abs x _)) = x
        suggest _		 = __IMPOSSIBLE__

compareTel :: MonadTCM tcm => Comparison -> Telescope -> Telescope -> tcm Constraints
compareTel cmp tel1 tel2 =
  verboseBracket "tc.conv.tel" 5 "compareTel" $
  catchConstraint (TelCmp cmp tel1 tel2) $ case (tel1, tel2) of
    (EmptyTel, EmptyTel) -> return []
    (EmptyTel, _)        -> bad
    (_, EmptyTel)        -> bad
    (ExtendTel arg1@(Arg h1 r1 a1) tel1, ExtendTel arg2@(Arg h2 r2 a2) tel2)
      | h1 /= h2 -> bad
      | otherwise -> do
          let (tel1', tel2') = raise 1 (tel1, tel2)
              arg            = Var 0 []
          name <- freshName_ (suggest (absName tel1) (absName tel2))
          cs   <- compareType cmp a1 a2
          let c = TelCmp cmp (absApp tel1' arg) (absApp tel2' arg)

	  let dependent = 0 `freeIn` absBody tel2

          if dependent
	    then addCtx name arg1 $ guardConstraint (return cs) c
	    else do cs' <- addCtx name arg1 $ solveConstraint c
		    return $ cs ++ cs'
          where
            suggest "_" y = y
            suggest  x  _ = x
  where
    bad = typeError $ UnequalTelescopes cmp tel1 tel2

-- | Syntax directed equality on atomic values
--
compareAtom :: MonadTCM tcm => Comparison -> Type -> Term -> Term -> tcm Constraints
compareAtom cmp t m n =
    verboseBracket "tc.conv.atom" 5 "compareAtom" $
    -- if a PatternErr is thrown, rebuild constraint!
    catchConstraint (ValueCmp cmp t m n) $ do
      -- constructorForm changes literal to constructors
      -- Andreas: what happens if I cut out the eta expansion here?
      -- Answer: Triggers issue 245, does not resolve 348
      mb <- traverse constructorForm =<< etaExpandBlocked =<< reduceB m
      nb <- traverse constructorForm =<< etaExpandBlocked =<< reduceB n
      let m = ignoreBlocking mb
          n = ignoreBlocking nb

          checkSyntacticEquality = do
            n <- normalise n    -- is this what we want?
            m <- normalise m
            if m == n
                then return []	-- Check syntactic equality for blocked terms
                else buildConstraint $ ValueCmp cmp t m n

      reportSDoc "tc.conv.atom" 10 $ fsep
	[ text "compareAtom", prettyTCM mb, prettyTCM cmp, prettyTCM nb, text ":", prettyTCM t ]
      case (mb, nb) of
        -- equate two metas x and y.  if y is the younger meta,
        -- try first y := x and then x := y
        (NotBlocked (MetaV x xArgs), NotBlocked (MetaV y yArgs))
            | x == y ->
              case intersectVars xArgs yArgs of
                -- all relevant arguments are variables
                Just kills -> do
                  killedAll <- killArgs kills x
                  if killedAll then return [] else checkSyntacticEquality
                -- not all relevant arguments are variables
                Nothing -> checkSyntacticEquality -- Check syntactic equality on meta-variables
                                -- (same as for blocked terms)
{-
            | x == y -> if   sameVars xArgs yArgs
                        then return []
                        else do -- Check syntactic equality on meta-variables
                                -- (same as for blocked terms)
                          m <- normalise m
                          n <- normalise n
                          if m == n
                            then return []
                            else buildConstraint (ValueCmp cmp t m n)
-}
            | otherwise -> do
                [p1, p2] <- mapM getMetaPriority [x,y]
                -- instantiate later meta variables first
                let (solve1, solve2)
                      | (p1,x) > (p2,y) = (l,r)
                      | otherwise	    = (r,l)
                      where l = assignV t x xArgs n
                            r = assignV t y yArgs m
                    try m fallback = do
                      cs <- m
                      case cs of
                        []	-> return []
                        _	-> fallback cs

                -- First try the one with the highest priority. If that doesn't
                -- work, try the low priority one. If that doesn't work either,
                -- go with the first version.
                rollback <- return . put =<< get
                try solve1 $ \cs -> do
                  undoRollback <- return . put =<< get
                  rollback
                  try solve2 $ \_ -> do
                    undoRollback
                    return cs

        -- one side a meta, the other an unblocked term
	(NotBlocked (MetaV x xArgs), _) -> assignV t x xArgs n
	(_, NotBlocked (MetaV x xArgs)) -> assignV t x xArgs m

        (Blocked{}, Blocked{})	-> checkSyntacticEquality
{-
            do
            n <- normalise n    -- is this what we want?
            m <- normalise m
            if m == n
                then return []	-- Check syntactic equality for blocked terms
                else buildConstraint $ ValueCmp cmp t m n
-}

        (Blocked{}, _)    -> useInjectivity cmp t m n
        (_,Blocked{})     -> useInjectivity cmp t m n
        _ -> case (m, n) of
	    _ | f1@(FunV _ _) <- funView m
	      , f2@(FunV _ _) <- funView n -> equalFun f1 f2

	    (Sort s1, Sort s2) -> compareSort CmpEq s1 s2

	    (Lit l1, Lit l2) | l1 == l2 -> return []
	    (Var i iArgs, Var j jArgs) | i == j -> do
		a <- typeOfBV i
                -- Variables are invariant in their arguments
		compareArgs [] a iArgs jArgs
	    (Def x xArgs, Def y yArgs) | x == y -> do
                pol <- getPolarity' cmp x
		reportSDoc "tc.conv.atom" 20 $
		  text "compareArgs" <+> sep
                    [ sep [ prettyTCM xArgs
			  , prettyTCM yArgs
			  ]
                    , nest 2 $ text (show pol)
                    ]
		a <- defType <$> getConstInfo x
		compareArgs pol a xArgs yArgs
	    (Con x xArgs, Con y yArgs)
		| x == y -> do
		    -- The type is a datatype or a record.
		    Def d args <- reduce $ unEl t
		    -- Get the number of parameters to the datatype (or record)
                    npars <- do
                      def <- theDef <$> getConstInfo d
                      case def of
		        Datatype{dataPars = npars} -> return npars
                        Record{recPars = npars}    -> return npars
                        _                          -> __IMPOSSIBLE__
		    -- The type to compare the arguments at is obtained by
		    -- instantiating the parameters.
		    a <- defType <$> getConstInfo x
		    let a' = piApply a (genericTake npars args)
                    -- Constructors are invariant in their arguments
                    -- (could be covariant).
                    compareArgs [] a' xArgs yArgs
            _ -> typeError $ UnequalTerms cmp m n t
    where
	equalFun (FunV arg1@(Arg h1 r1 a1) t1) (FunV (Arg h2 r2 a2) t2)
	    | h1 /= h2	= typeError $ UnequalHiding ty1 ty2
            -- Andreas 2010-09-21 compare r1 and r2, but ignore forcing annotations!
	    | ignoreForced r1 /= ignoreForced r2 = typeError $ UnequalRelevance ty1 ty2
	    | otherwise = do
		    let (ty1',ty2') = raise 1 (ty1,ty2)
			arg	    = Arg h1 r1 (Var 0 [])
		    name <- freshName_ (suggest t1 t2)
		    cs   <- compareType cmp a2 a1
		    let c = TypeCmp cmp (piApply ty1' [arg]) (piApply ty2' [arg])

		    -- We only need to require a1 == a2 if t2 is a dependent function type.
		    -- If it's non-dependent it doesn't matter what we add to the context.
		    let dependent = case t2 of
					Pi _ _	-> True
					Fun _ _	-> False
					_	-> __IMPOSSIBLE__
		    if dependent
			then addCtx name arg1 $ guardConstraint (return cs) c
			else do
			    cs' <- addCtx name arg1 $ solveConstraint c
			    return $ cs ++ cs'
	    where
		ty1 = El (getSort a1) t1    -- TODO: wrong (but it doesn't matter)
		ty2 = El (getSort a2) t2
		suggest t1 t2 = case concatMap name [t1,t2] of
				    []	-> "_"
				    x:_	-> x
		    where
			name (Pi _ (Abs x _)) = [x]
			name (Fun _ _)	      = []
			name _		      = __IMPOSSIBLE__
	equalFun _ _ = __IMPOSSIBLE__



-- | Type-directed equality on argument lists
--
compareArgs :: MonadTCM tcm => [Polarity] -> Type -> Args -> Args -> tcm Constraints
compareArgs _ _ [] [] = return []
compareArgs _ _ [] (_:_) = __IMPOSSIBLE__
compareArgs _ _ (_:_) [] = __IMPOSSIBLE__
compareArgs pols0 a (arg1 : args1) (arg2 : args2) =
    verboseBracket "tc.conv.args" 5 "compareArgs" $ do
    let (pol, pols) = nextPolarity pols0
    a <- reduce a
    catchConstraint (ArgsCmp pols0 a (arg1 : args1) (arg2 : args2)) $ do
    reportSDoc "tc.conv.args" 30 $
      sep [ text "compareArgs"
          , nest 2 $ sep [ prettyTCM (arg1 : args1)
                         , prettyTCM (arg2 : args2)
                         ]
          , nest 2 $ text ":" <+> prettyTCM a
          ]
    case funView (unEl a) of
	FunV (Arg _ r b) _ -> do
	    reportSDoc "tc.conv.args" 10 $
              sep [ text "compareArgs" <+> parens (text $ show pol ++ " " ++ show r)
                  , nest 2 $ sep [ prettyTCM arg1
                                 , text "~~" <+> prettyTCM arg2
                                 , text ":" <+> prettyTCM b
                                 ]
                  ]
            let cmp x y = case pol of
                            Invariant     -> compareTerm CmpEq b x y
                            Covariant     -> compareTerm CmpLeq b x y
                            Contravariant -> compareTerm CmpLeq b y x
            cs1 <- case r of
                    Forced     -> return []
                    Irrelevant -> return [] -- Andreas: ignore irr. func. args.
                    Relevant   -> cmp (unArg arg1) (unArg arg2)
            -- mlvl <- mlevel
	    case (cs1, unEl a) of
                                -- We can safely ignore sort annotations here
                                -- (except it's not, we risk leaving unsolved sorts)
                                -- We're also ignoring levels which isn't quite as
                                -- safe (it would be if we disallowed matching on levels?)
		(_:_, Pi (Arg _ _ (El _ lvl')) c) | 0 `freeInIgnoringSorts` absBody c
                                                  -- && Just lvl' /= mlvl
		    -> do
                        reportSDoc "tc.conv.args" 15 $ sep
                          [ text "aborting compareArgs" <+> parens (text $ show pol)
                          , nest 2 $ fsep
                              [ prettyTCM arg1
                              , text "~~" <+> prettyTCM arg2
                              , text ":" <+> prettyTCM b
                              , text "--->" <+> prettyTCM cs1
                              ]
                          ]
                        patternViolation
		_   -> do
                    reportSDoc "tc.conv.args" 15 $ sep
                      [ text "compareArgs" <+> parens (text $ show pol)
                      , nest 2 $ sep
                        [ prettyTCM args1
                        , text "~~" <+> prettyTCM args2
                        , text ":" <+> prettyTCM (piApply a [arg1])
                        ]
                      ]
		    cs2 <- compareArgs pols (piApply a [arg1]) args1 args2
		    return $ cs1 ++ cs2
        _   -> patternViolation

-- | Equality on Types
compareType :: MonadTCM tcm => Comparison -> Type -> Type -> tcm Constraints
compareType cmp ty1@(El s1 a1) ty2@(El s2 a2) =
    verboseBracket "tc.conv.type" 5 "compareType" $
    catchConstraint (TypeCmp cmp ty1 ty2) $ do
	reportSDoc "tc.conv.type" 9 $ vcat
          [ hsep [ text "compareType", prettyTCM ty1, prettyTCM cmp, prettyTCM ty2 ]
          , hsep [ text "   sorts:", prettyTCM s1, text " and ", prettyTCM s2 ]
          ]
	cs1 <- compareSort CmpEq s1 s2 `catchError` \err -> case errError err of
                  TypeError _ _ -> do
                    reportSDoc "tc.conv.type" 10 $ vcat
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
                    throwError err
                  _             -> throwError err
	cs2 <- compareTerm cmp (sort s1) a1 a2
        cs  <- solveConstraints $ cs1 ++ cs2
        unless (null cs) $
          reportSDoc "tc.conv.type" 9 $
            text "   --> " <+> prettyTCM cs
	return cs

leqType :: MonadTCM tcm => Type -> Type -> tcm Constraints
leqType = compareType CmpLeq

---------------------------------------------------------------------------
-- * Sorts
---------------------------------------------------------------------------

compareSort :: MonadTCM tcm => Comparison -> Sort -> Sort -> tcm Constraints
compareSort CmpEq  = equalSort
compareSort CmpLeq = leqSort
  -- TODO: change to leqSort when we have better constraint solving
  --       or not? might not be needed if we get universe polymorphism
  --       leqSort is still used when checking datatype declarations though

-- | Check that the first sort is less or equal to the second.
leqSort :: MonadTCM tcm => Sort -> Sort -> tcm Constraints
leqSort s1 s2 =
  ifM typeInType (return []) $
    catchConstraint (SortCmp CmpLeq s1 s2) $
    do	(s1,s2) <- reduce (s1,s2)
        reportSDoc "tc.conv.sort" 10 $
          sep [ text "leqSort"
              , nest 2 $ fsep [ prettyTCM s1 <+> text "=<"
                              , prettyTCM s2 ]
              ]
	case (s1,s2) of

            -- New universe polymorphism
--             (Type a  , Type b  )             -> compareLevel CmpLeq a b

	    (Type (Lit (LitLevel _ n)), Type (Lit (LitLevel _ m)))
              | n <= m    -> return []
	      | otherwise -> notLeq s1 s2
            (Type a, Type b) -> leqLevel a b

	    (Prop    , Prop    )	     -> return []
	    (Type _  , Prop    )	     -> notLeq s1 s2
	    (Suc _   , Prop    )	     -> notLeq s1 s2

	    (Prop    , Type _  )	     -> return []

	    (Suc s   , Type (Lit (LitLevel _ n)))
              | 1 <= n    -> leqSort s (mkType $ n - 1)
	    (Suc s   , Type b  ) -> notLeq s1 s2  -- TODO
            (Suc s1  , Suc s2  ) -> leqSort s1 s2 -- TODO: not what we want for Prop(?)
	    (_	     , Suc _   )	     -> equalSort s1 s2

	    (Lub a b , _       )	     -> liftM2 (++) (leqSort a s2) (leqSort b s2)
	    (_	     , Lub _ _ )	     -> equalSort s1 s2

	    (MetaS{} , _       )	     -> equalSort s1 s2
	    (_	     , MetaS{} )	     -> equalSort s1 s2
            (Inf     , Inf     )             -> return []
            (Inf     , _       )             -> notLeq s1 s2
            (_       , Inf     )             -> return []
            (DLub{}  , _       )             -> equalSort s1 s2
            (_       , DLub{}  )             -> equalSort s1 s2
    where
	notLeq s1 s2 = typeError $ NotLeqSort s1 s2

leqLevel :: MonadTCM tcm => Term -> Term -> tcm Constraints
leqLevel a b = liftTCM $ do
  reportSDoc "tc.conv.nat" 10 $
    text "compareLevel" <+>
      sep [ prettyTCM a <+> text "=<"
          , prettyTCM b ]
  n <- levelView a
  m <- levelView b
  leqView n m
  where
    leqView n@(Max as) m@(Max bs) = do
      reportSDoc "tc.conv.nat" 10 $
        text "compareLevelView" <+>
          sep [ text (show n) <+> text "=<"
              , text (show m) ]
      case (as, bs) of
        (_, [])  -> concat <$> sequence [ leqPlusView a (ClosedLevel 0) | a <- as ]
        (_, [b]) -> concat <$> sequence [ leqPlusView a b | a <- as ]
        _        -> do
          -- Each a needs to be less than at least one of the b's
          sequence [ choice [ leqPlusView a b | b <- bs ] | a <- as ]
          return []
    leqPlusView n m = do
      reportSDoc "tc.conv.nat" 10 $
        text "comparePlusView" <+>
          sep [ text (show n) <+> text "=<"
              , text (show m) ]
      case (n, m) of
        -- Both closed
        (ClosedLevel n, ClosedLevel m)
          | n <= m -> ok

        -- Both neutral
        (Plus n (NeutralLevel a), Plus m (NeutralLevel b))
          | n <= m -> do
            lvl <- primLevel
            equalTerm (El (mkType 0) lvl) a b

        -- closed ≤ any
        (ClosedLevel n, Plus m _)
          | n <= m -> ok

        -- Any blocked or meta
        (Plus _ BlockedLevel{}, _) -> postpone
        (_, Plus _ BlockedLevel{}) -> postpone
        (Plus _ MetaLevel{}, _)    -> postpone
        (_, Plus _ MetaLevel{})    -> postpone

        _ -> notok
    ok       = return []
    notok    = typeError $ NotLeqSort (Type a) (Type b)
    postpone = patternViolation

    choice []     = patternViolation
    choice (m:ms) = noConstraints m `catchError` \_ -> choice ms
--       case errError e of
--         PatternErr{} -> choice ms
--         _            -> throwError e

equalLevel :: MonadTCM tcm => Term -> Term -> tcm Constraints
equalLevel a b = do
  lvl    <- primLevel
  Max as <- levelView a
  Max bs <- levelView b
  a <- unLevelView (Max as)
  b <- unLevelView (Max bs)
  liftTCM $ catchConstraint (ValueCmp CmpEq (El (mkType 0) lvl) a b)
          $ check a b as bs
  where
    check a b as bs = do
      reportSDoc "tc.conv.nat" 20 $
        sep [ text "equalLevel"
            , nest 2 $ sep [ prettyTCM a <+> text "=="
                           , prettyTCM b
                           ]
            , nest 2 $ sep [ text (show (Max as)) <+> text "=="
                           , text (show (Max bs))
                           ]
            ]
      let a === b   = do
            lvl <- getLvl
            equalAtom lvl a b
          as =!= bs = do a <- unLevelView (Max as)
                         b <- unLevelView (Max bs)
                         a === b
      case (as, bs) of
        _ | List.sort as == List.sort bs -> ok
          | any isBlocked (as ++ bs) -> do
              lvl <- getLvl
              liftTCM $ useInjectivity CmpEq lvl a b

        -- 0 == any
        ([], _) -> wrap $ concat <$> sequence [ as =!= [b] | b <- bs ]
        (_, []) -> wrap $ concat <$> sequence [ [a] =!= bs | a <- as ]

        -- closed == closed
        ([ClosedLevel n], [ClosedLevel m])
          | n == m    -> ok
          | otherwise -> notok

        -- closed == neutral
        ([ClosedLevel{}], _) | any isNeutral bs -> notok
        (_, [ClosedLevel{}]) | any isNeutral as -> notok

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
        ok       = return []
        notok    = typeError $ UnequalSorts (Type a) (Type b)
        postpone = patternViolation

        getLvl = El (mkType 0) <$> primLevel

        meta n x as bs = do
          bs' <- mapM (subtr n) bs
          lvl <- getLvl
          assignV lvl x as =<< unLevelView (Max bs')

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
equalSort :: MonadTCM tcm => Sort -> Sort -> tcm Constraints
equalSort s1 s2 =
  ifM typeInType (return []) $
    catchConstraint (SortCmp CmpEq s1 s2) $ do
        (s1,s2) <- reduce (s1,s2)
        reportSDoc "tc.conv.sort" 10 $
          sep [ text "equalSort"
              , nest 2 $ fsep [ prettyTCM s1 <+> text "=="
                              , prettyTCM s2 ]
              ]
	case (s1,s2) of

            -- New universe polymorphism
--             (Type a, Type b) -> compareLevel CmpEq a b

            (Type (Lit n), Type (Lit m))
              | n == m           -> return []
              | otherwise        -> notEq s1 s2
            (Type a  , Type b  ) -> equalLevel a b

	    (MetaS x us , MetaS y vs) -> do
              s1 <- normalise s1
              s2 <- normalise s2
              if s1 == s2 then return []
			  else do
		[p1, p2] <- mapM getMetaPriority [x, y]
		if p1 >= p2 then assignS x us s2
			    else assignS y vs s1
	    (MetaS x vs, _       ) -> assignS x vs s2
	    (_	     , MetaS{} ) -> equalSort s2 s1

	    (Prop    , Prop    ) -> return []
	    (Type _  , Prop    ) -> notEq s1 s2
	    (Prop    , Type _  ) -> notEq s1 s2

	    (Suc s   , Prop    ) -> notEq s1 s2
	    (Suc s   , Type (Lit (LitLevel _ 0))) -> notEq s1 s2
	    (Suc s   , Type (Lit (LitLevel _ 1))) -> buildConstraint (SortCmp CmpEq s1 s2)
	    (Suc s   , Type (Lit (LitLevel _ n))) -> equalSort s (mkType $ n - 1)
	    (Prop    , Suc s   ) -> notEq s1 s2
	    (Type (Lit (LitLevel _ 0))  , Suc s   ) -> notEq s1 s2
	    (Type (Lit (LitLevel _ 1))  , Suc s   ) -> buildConstraint (SortCmp CmpEq s1 s2)
	    (Type (Lit (LitLevel _ n))  , Suc s   ) -> equalSort (mkType $ n - 1) s
            (Suc s1  , Suc s2  ) -> equalSort s1 s2 -- TODO: not what we want for Prop(?)
	    (_	     , Suc _   ) -> buildConstraint (SortCmp CmpEq s1 s2)
	    (Suc _   , _       ) -> buildConstraint (SortCmp CmpEq s1 s2)

            (Inf     , Inf     )             -> return []
            (Inf     , _       )             -> notEq s1 s2
            (_       , Inf     )             -> notEq s1 s2
            (s0@(Type (Lit (LitLevel _ 0))), Lub s1 s2) -> do
              cs1 <- equalSort s0 s1
              cs2 <- equalSort s0 s2
              return $ cs1 ++ cs2
            (Lub s1 s2, s0@(Type (Lit (LitLevel _ 0)))) -> do
              cs1 <- equalSort s1 s0
              cs2 <- equalSort s2 s0
              return $ cs1 ++ cs2
            (Lub{}   , Lub{}   ) -> do
              (s1, s2) <- normalise (s1, s2)
              if s1 == s2
                then return []
                else buildConstraint (SortCmp CmpEq s1 s2)
	    (Lub _ _ , _       ) -> buildConstraint (SortCmp CmpEq s1 s2)
	    (_	     , Lub _ _ ) -> buildConstraint (SortCmp CmpEq s1 s2)

            (DLub s1 s2, s0@(Type (Lit (LitLevel _ 0)))) -> do
              cs1 <- equalSort s1 s0
              cs2 <- underAbstraction_ s2 $ \s2 -> equalSort s2 s0
              return $ cs1 ++ cs2
            (s0@(Type (Lit (LitLevel _ 0))), DLub s1 s2) -> do
              cs1 <- equalSort s0 s1
              cs2 <- underAbstraction_ s2 $ \s2 -> equalSort s0 s2
              return $ cs1 ++ cs2
            (DLub{}  , _       )             -> buildConstraint (SortCmp CmpEq s1 s2)
            (_       , DLub{}  )             -> buildConstraint (SortCmp CmpEq s1 s2)
    where
	notEq s1 s2 = typeError $ UnequalSorts s1 s2
