{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Conversion where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet

#if __GLASGOW_HASKELL__ <= 708
import Data.Traversable ( traverse )
#endif

import Agda.Syntax.Abstract.Views (isSet)
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Translation.InternalToAbstract (reify)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.CompiledClause (CompiledClauses'(Fail))
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.MetaVars.Occurs (killArgs,PruneResult(..),rigidVarsNotContainedIn)
import Agda.TypeChecking.Names
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import qualified Agda.TypeChecking.SyntacticEquality as SynEq
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Constraints
import {-# SOURCE #-} Agda.TypeChecking.CheckInternal (infer)
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Forcing (isForced, nextIsForced)
import Agda.TypeChecking.Free
import Agda.TypeChecking.Datatypes (getConType, getFullyAppliedConType)
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Level
import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.ProjectionLike (elimView)
import Agda.TypeChecking.Primitive
import Agda.Interaction.Options

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.Functor
import Agda.Utils.Monad
import Agda.Utils.Maybe
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible

-- | Try whether a computation runs without errors or new constraints
--   (may create new metas, though).
--   Restores state upon failure.
tryConversion :: TCM () -> TCM Bool
tryConversion = isJust <.> tryConversion'

-- | Try whether a computation runs without errors or new constraints
--   (may create new metas, though).
--   Return 'Just' the result upon success.
--   Return 'Nothing' and restore state upon failure.
tryConversion' :: TCM a -> TCM (Maybe a)
tryConversion' m = tryMaybe $ disableDestructiveUpdate $ noConstraints m

-- | Check if to lists of arguments are the same (and all variables).
--   Precondition: the lists have the same length.
sameVars :: Elims -> Elims -> Bool
sameVars xs ys = and $ zipWith same xs ys
    where
        same (Apply (Arg _ (Var n []))) (Apply (Arg _ (Var m []))) = n == m
        same _ _ = False

-- | @intersectVars us vs@ checks whether all relevant elements in @us@ and @vs@
--   are variables, and if yes, returns a prune list which says @True@ for
--   arguments which are different and can be pruned.
intersectVars :: Elims -> Elims -> Maybe [Bool]
intersectVars = zipWithM areVars where
    -- ignore irrelevant args
    areVars (Apply u) v | isIrrelevant u = Just False -- do not prune
    areVars (Apply (Arg _ (Var n []))) (Apply (Arg _ (Var m []))) = Just $ n /= m -- prune different vars
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
convError err = ifM ((==) Irrelevant <$> asksTC envRelevance) (return ()) $ typeError err

-- | Type directed equality on values.
--
compareTerm :: Comparison -> Type -> Term -> Term -> TCM ()
  -- If one term is a meta, try to instantiate right away. This avoids unnecessary unfolding.
  -- Andreas, 2012-02-14: This is UNSOUND for subtyping!
compareTerm cmp a u v = do
  reportSDoc "tc.conv.term" 10 $ sep
    [ "compareTerm"
    , nest 2 $ prettyTCM u <+> prettyTCM cmp <+> prettyTCM v
    , nest 2 $ ":" <+> prettyTCM a
    ]
  -- Check syntactic equality. This actually saves us quite a bit of work.
  ((u, v), equal) <- SynEq.checkSyntacticEquality u v
  -- OLD CODE, traverses the *full* terms u v at each step, even if they
  -- are different somewhere.  Leads to infeasibility in issue 854.
  -- (u, v) <- instantiateFull (u, v)
  -- let equal = u == v
  unifyPointers cmp u v $ if equal then verboseS "profile.sharing" 20 $ tick "equal terms" else do
      verboseS "profile.sharing" 20 $ tick "unequal terms"
      reportSDoc "tc.conv.term" 15 $ sep
        [ "compareTerm (not syntactically equal)"
        , nest 2 $ prettyTCM u <+> prettyTCM cmp <+> prettyTCM v
        , nest 2 $ ":" <+> prettyTCM a
        ]
      -- If we are at type Size, we cannot short-cut comparison
      -- against metas by assignment.
      -- Andreas, 2014-04-12: this looks incomplete.
      -- It seems to assume we are never comparing
      -- at function types into Size.
      let fallback = compareTerm' cmp a u v
          unlessSubtyping cont =
              if cmp == CmpEq then cont else do
                -- Andreas, 2014-04-12 do not short cut if type is blocked.
                ifBlockedType a (\ _ _ -> fallback) {-else-} $ \ _ a -> do
                  -- do not short circuit size comparison!
                  caseMaybeM (isSizeType a) cont (\ _ -> fallback)

          dir = fromCmp cmp
          rid = flipCmp dir     -- The reverse direction.  Bad name, I know.
      case (u, v) of
        (MetaV x us, MetaV y vs)
          | x /= y    -> unlessSubtyping $ solve1 `orelse` solve2 `orelse` compareTerm' cmp a u v
          | otherwise -> fallback
          where
            (solve1, solve2) | x > y     = (assign dir x us v, assign rid y vs u)
                             | otherwise = (assign rid y vs u, assign dir x us v)
        (MetaV x us, _) -> unlessSubtyping $ assign dir x us v `orelse` fallback
        (_, MetaV y vs) -> unlessSubtyping $ assign rid y vs u `orelse` fallback
        _               -> fallback
  where
    assign dir x es v = do
      -- Andreas, 2013-10-19 can only solve if no projections
      reportSDoc "tc.conv.term.shortcut" 20 $ sep
        [ "attempting shortcut"
        , nest 2 $ prettyTCM (MetaV x es) <+> ":=" <+> prettyTCM v
        ]
      ifM (isInstantiatedMeta x) patternViolation {-else-} $ do
        assignE dir x es v $ compareTermDir dir a
      reportSDoc "tc.conv.term.shortcut" 50 $
        "shortcut successful" $$ nest 2 ("result:" <+> (pretty =<< instantiate (MetaV x es)))
    -- Should be ok with catchError_ but catchError is much safer since we don't
    -- rethrow errors.
    orelse m h = catchError m (\_ -> h)

unifyPointers :: Comparison -> Term -> Term -> TCM () -> TCM ()
unifyPointers _ _ _ action = action
-- unifyPointers cmp _ _ action | cmp /= CmpEq = action
-- unifyPointers _ u v action = do
--   reportSLn "tc.ptr.unify" 50 $ "Maybe unifying pointers\n  u = " ++ show u ++ "\n  v = " ++ show v
--   old <- useTC stDirty
--   stDirty `setTCLens` False
--   action
--   reportSLn "tc.ptr.unify" 50 $ "Finished comparison\n  u = " ++ show u ++ "\n  v = " ++ show v
--   (u, v) <- instantiate (u, v)
--   reportSLn "tc.ptr.unify" 50 $ "After instantiation\n  u = " ++ show u ++ "\n  v = " ++ show v
--   dirty <- useTC stDirty
--   stDirty `setTCLens` old
--   if dirty then verboseS "profile.sharing" 20 (tick "unifyPtr: dirty")
--            else do
--             verboseS "profile.sharing" 20 (tick "unifyPtr: clean")
--             reportSLn "tc.ptr.unify" 80 $ "Unifying\n  u = " ++ show u ++ "\n  v = " ++ show v
--             forceEqualTerms u v
--             reportSLn "tc.ptr.unify" 80 $ "After unification\n  u = " ++ show u ++ "\n  v = " ++ show v

-- | Try to assign meta.  If meta is projected, try to eta-expand
--   and run conversion check again.
assignE :: CompareDirection -> MetaId -> Elims -> Term -> (Term -> Term -> TCM ()) -> TCM ()
assignE dir x es v comp = assignWrapper dir x es v $ do
  case allApplyElims es of
    Just vs -> assignV dir x vs v
    Nothing -> do
      reportSDoc "tc.conv.assign" 30 $ sep
        [ "assigning to projected meta "
        , prettyTCM x <+> sep (map prettyTCM es) <+> text (":" ++ show dir) <+> prettyTCM v
        ]
      etaExpandMeta [Records] x
      res <- isInstantiatedMeta' x
      case res of
        Just u  -> do
          reportSDoc "tc.conv.assign" 30 $ sep
            [ "seems like eta expansion instantiated meta "
            , prettyTCM x <+> text  (":" ++ show dir) <+> prettyTCM u
            ]
          let w = u `applyE` es
          comp w v
        Nothing ->  do
          reportSLn "tc.conv.assign" 30 "eta expansion did not instantiate meta"
          patternViolation  -- nothing happened, give up

compareTermDir :: CompareDirection -> Type -> Term -> Term -> TCM ()
compareTermDir dir a = dirToCmp (`compareTerm'` a) dir

compareTerm' :: Comparison -> Type -> Term -> Term -> TCM ()
compareTerm' cmp a m n =
  verboseBracket "tc.conv.term" 20 "compareTerm" $ do
  a' <- reduce a
  catchConstraint (ValueCmp cmp a' m n) $ do
    reportSDoc "tc.conv.term" 30 $ fsep
      [ "compareTerm", prettyTCM m, prettyTCM cmp, prettyTCM n, ":", prettyTCM a' ]
    propIrr  <- isPropEnabled
    isSize   <- isJust <$> isSizeType a'
    s        <- reduce $ getSort a'
    mlvl     <- tryMaybe primLevel
    reportSDoc "tc.conv.level" 60 $ nest 2 $ sep
      [ "a'   =" <+> pretty a'
      , "mlvl =" <+> pretty mlvl
      , text $ "(Just (unEl a') == mlvl) = " ++ show (Just (unEl a') == mlvl)
      ]
    case s of
      Prop{} | propIrr -> compareIrrelevant a' m n
      _    | isSize   -> compareSizes cmp m n
      _               -> case unEl a' of
        a | Just a == mlvl -> do
          a <- levelView m
          b <- levelView n
          equalLevel a b
        a@Pi{}    -> equalFun s a m n
        Lam _ _   -> __IMPOSSIBLE__
        Def r es  -> do
          isrec <- isEtaRecord r
          if isrec
            then do
              sig <- getSignature
              let ps = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
              -- Andreas, 2010-10-11: allowing neutrals to be blocked things does not seem
              -- to change Agda's behavior
              --    isNeutral Blocked{}          = False
                  isNeutral (NotBlocked _ Con{}) = return False
              -- Andreas, 2013-09-18 / 2015-06-29: a Def by copatterns is
              -- not neutral if it is blocked (there can be missing projections
              -- to trigger a reduction.
                  isNeutral (NotBlocked r (Def q _)) = do    -- Andreas, 2014-12-06 optimize this using r !!
                    not <$> usesCopatterns q -- a def by copattern can reduce if projected
                  isNeutral _                   = return True
                  isMeta (NotBlocked _ MetaV{}) = True
                  isMeta _                      = False

              reportSDoc "tc.conv.term" 30 $ prettyTCM a <+> "is eta record type"
              m <- reduceB m
              mNeutral <- isNeutral m
              n <- reduceB n
              nNeutral <- isNeutral n
              case (m, n) of
                _ | isMeta m || isMeta n ->
                    compareAtom cmp a' (ignoreBlocking m) (ignoreBlocking n)

                _ | mNeutral && nNeutral -> do
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
                  -- Record constructors are covariant (see test/succeed/CovariantConstructors).
                  compareArgs (repeat $ polFromCmp cmp) [] (telePi_ tel __DUMMY_TYPE__) (Con c ConOSystem []) m' n'

            else (do pathview <- pathView a'
                     equalPath pathview a' m n)
        _ -> compareAtom cmp a' m n
  where
    -- equality at function type (accounts for eta)
    equalFun :: Sort -> Term -> Term -> Term -> TCM ()
    equalFun s a@(Pi dom b) m n | domFinite dom = do
       mp <- fmap getPrimName <$> getBuiltin' builtinIsOne
       case unEl $ unDom dom of
          Def q [Apply phi]
              | Just q == mp -> compareTermOnFace cmp (unArg phi) (El s (Pi (dom {domFinite = False}) b)) m n
          _                  -> equalFun s (Pi (dom{domFinite = False}) b) m n
    equalFun _ (Pi dom@Dom{domInfo = info} b) m n | not $ domFinite dom = do
        name <- freshName_ $ suggest (absName b) ("x" :: String)
        addContext (name, dom) $ compareTerm cmp (absBody b) m' n'
      where
        (m',n') = raise 1 (m,n) `apply` [Arg info $ var 0]
    equalFun _ _ _ _ = __IMPOSSIBLE__

    equalPath :: PathView -> Type -> Term -> Term -> TCM ()
    equalPath (PathType s _ l a x y) _ m n = do
        name <- freshName_ ("i" :: String)
        interval <- el primInterval
        let (m',n') = raise 1 (m, n) `applyE` [IApply (raise 1 $ unArg x) (raise 1 $ unArg y) (var 0)]
        addContext (name, defaultDom interval) $ compareTerm cmp (El (raise 1 s) $ (raise 1 $ unArg a) `apply` [argN $ var 0]) m' n'
    equalPath OType{} a' m n = cmpDef a' m n

    cmpDef a'@(El s ty) m n = do
       mI     <- getBuiltinName'   builtinInterval
       mIsOne <- getBuiltinName'   builtinIsOne
       mGlue  <- getPrimitiveName' builtinGlue
       mSub   <- getBuiltinName' builtinSub
       case ty of
         Def q es | Just q == mIsOne -> return ()
         Def q es | Just q == mGlue, Just args@(l:_:a:phi:_) <- allApplyElims es -> do
              ty <- el' (pure $ unArg l) (pure $ unArg a)
              unglue <- prim_unglue
              let mkUnglue m = apply unglue $ map (setHiding Hidden) args ++ [argN m]
              reportSDoc "conv.glue" 20 $ prettyTCM (ty,mkUnglue m,mkUnglue n)
              compareTermOnFace cmp (unArg phi) ty m n
              compareTerm cmp ty (mkUnglue m) (mkUnglue n)
         Def q es | Just q == mSub, Just args@(l:a:_) <- allApplyElims es -> do
              ty <- el' (pure $ unArg l) (pure $ unArg a)
              out <- primSubOut
              let mkOut m = apply out $ map (setHiding Hidden) args ++ [argN m]
              compareTerm cmp ty (mkOut m) (mkOut n)
         Def q [] | Just q == mI -> compareInterval cmp a' m n
         _ -> compareAtom cmp a' m n

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
    (ExtendTel dom1{-@(Dom i1 a1)-} tel1, ExtendTel dom2{-@(Dom i2 a2)-} tel2) -> do
      compareDom cmp dom1 dom2 tel1 tel2 bad bad $
        compareTel t1 t2 cmp (absBody tel1) (absBody tel2)
  where
    -- Andreas, 2011-05-10 better report message about types
    bad = typeError $ UnequalTypes cmp t2 t1
      -- switch t2 and t1 because of contravariance!



-- | Raise 'UnequalTerms' if there is no hope that by
--   meta solving and subsequent eta-contraction these
--   terms could become equal.
--   Precondition: the terms are in reduced form
--   (with no top-level pointer) and
--   failed to be equal in the 'compareAtom' check.
--
--   By eta-contraction, a lambda or a record constructor term
--   can become anything.
etaInequal :: Comparison -> Type -> Term -> Term -> TCM ()
etaInequal cmp t m n = do
  let inequal  = typeError $ UnequalTerms cmp m n t
      dontKnow = do
        reportSDoc "tc.conv.inequal" 20 $ hsep
          [ "etaInequal: postponing "
          , prettyTCM m
          , " != "
          , prettyTCM n
          ]
        patternViolation
  -- if type is not blocked, then we would have tried eta already
  flip (ifBlockedType t) (\ _ _ -> inequal) $ \ _ _ -> do
    -- type is blocked
    case (m, n) of
      (Con{}, _) -> dontKnow
      (_, Con{}) -> dontKnow
      (Lam{}, _) -> dontKnow
      (_, Lam{}) -> dontKnow
      _          -> inequal

compareAtomDir :: CompareDirection -> Type -> Term -> Term -> TCM ()
compareAtomDir dir a = dirToCmp (`compareAtom` a) dir

-- | Compute the head type of an elimination. For projection-like functions
--   this requires inferring the type of the principal argument.
computeElimHeadType :: QName -> Elims -> Elims -> TCM Type
computeElimHeadType f es es' = do
  def <- getConstInfo f
  -- To compute the type @a@ of a projection-like @f@,
  -- we have to infer the type of its first argument.
  if projectionArgs (theDef def) <= 0 then return $ defType def else do
    -- Find an first argument to @f@.
    let arg = case (es, es') of
              (Apply arg : _, _) -> arg
              (_, Apply arg : _) -> arg
              _ -> __IMPOSSIBLE__
    -- Infer its type.
    reportSDoc "tc.conv.infer" 30 $
      "inferring type of internal arg: " <+> prettyTCM arg
    targ <- infer $ unArg arg
    reportSDoc "tc.conv.infer" 30 $
      "inferred type: " <+> prettyTCM targ
    -- getDefType wants the argument type reduced.
    -- Andreas, 2016-02-09, Issue 1825: The type of arg might be
    -- a meta-variable, e.g. in interactive development.
    -- In this case, we postpone.
    fromMaybeM patternViolation $ getDefType f =<< reduce targ

-- | Syntax directed equality on atomic values
--
compareAtom :: Comparison -> Type -> Term -> Term -> TCM ()
compareAtom cmp t m n =
  verboseBracket "tc.conv.atom" 20 "compareAtom" $
  -- if a PatternErr is thrown, rebuild constraint!
  catchConstraint (ValueCmp cmp t m n) $ do
    reportSDoc "tc.conv.atom" 50 $
      "compareAtom" <+> fsep [ prettyTCM m <+> prettyTCM cmp
                                  , prettyTCM n
                                  , ":" <+> prettyTCM t ]
    -- Andreas: what happens if I cut out the eta expansion here?
    -- Answer: Triggers issue 245, does not resolve 348
    (mb',nb') <- ifM (asksTC envCompareBlocked) ((notBlocked -*- notBlocked) <$> reduce (m,n)) $ do
      mb' <- etaExpandBlocked =<< reduceB m
      nb' <- etaExpandBlocked =<< reduceB n
      return (mb', nb')

    -- constructorForm changes literal to constructors
    -- only needed if the other side is not a literal
    (mb'', nb'') <- case (ignoreBlocking mb', ignoreBlocking nb') of
      (Lit _, Lit _) -> return (mb', nb')
      _ -> (,) <$> traverse constructorForm mb'
               <*> traverse constructorForm nb'

    mb <- traverse unLevel mb''
    nb <- traverse unLevel nb''

    let m = ignoreBlocking mb
        n = ignoreBlocking nb

        postpone = addConstraint $ ValueCmp cmp t m n

        checkSyntacticEquality =
          ifNotM (optSyntacticEquality <$> pragmaOptions) postpone $ do
          n <- normalise n    -- is this what we want?
          m <- normalise m
          if m == n
              then return ()  -- Check syntactic equality for blocked terms
              else postpone

        dir = fromCmp cmp
        rid = flipCmp dir     -- The reverse direction.  Bad name, I know.

        assign dir x es v = assignE dir x es v $ compareAtomDir dir t

    unifyPointers cmp (ignoreBlocking mb') (ignoreBlocking nb') $ do    -- this needs to go after eta expansion to avoid creating infinite terms

      reportSDoc "tc.conv.atom" 30 $
        "compareAtom" <+> fsep [ prettyTCM mb <+> prettyTCM cmp
                                    , prettyTCM nb
                                    , ":" <+> prettyTCM t ]
      reportSDoc "tc.conv.atom" 80 $
        "compareAtom" <+> fsep [ (text . show) mb <+> prettyTCM cmp
                                    , (text . show) nb
                                    , ":" <+> (text . show) t ]
      case (mb, nb) of
        -- equate two metas x and y.  if y is the younger meta,
        -- try first y := x and then x := y
        (NotBlocked _ (MetaV x xArgs), NotBlocked _ (MetaV y yArgs))
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
                -- not all relevant arguments are variables
                Nothing -> checkSyntacticEquality -- Check syntactic equality on meta-variables
                                -- (same as for blocked terms)
            | otherwise -> do
                [p1, p2] <- mapM getMetaPriority [x,y]
                -- First try the one with the highest priority. If that doesn't
                -- work, try the low priority one.
                let (solve1, solve2)
                      | (p1, x) > (p2, y) = (l1, r2)
                      | otherwise         = (r1, l2)
                      where l1 = assign dir x xArgs n
                            r1 = assign rid y yArgs m
                            -- Careful: the first attempt might prune the low
                            -- priority meta! (Issue #2978)
                            l2 = ifM (isInstantiatedMeta x) (compareTermDir dir t m n) l1
                            r2 = ifM (isInstantiatedMeta y) (compareTermDir rid t n m) r1

                    try m h = m `catchError_` \err -> case err of
                      PatternErr{} -> h
                      _            -> throwError err

                try solve1 solve2

        -- one side a meta, the other an unblocked term
        (NotBlocked _ (MetaV x es), _) -> assign dir x es n
        (_, NotBlocked _ (MetaV x es)) -> assign rid x es m
        (Blocked{}, Blocked{})  -> checkSyntacticEquality
        (Blocked{}, _)  -> useInjectivity (fromCmp cmp) t m n   -- The blocked term goes first
        (_, Blocked{})  -> useInjectivity (flipCmp $ fromCmp cmp) t n m
        _ -> do
          -- -- Andreas, 2013-10-20 put projection-like function
          -- -- into the spine, to make compareElims work.
          -- -- 'False' means: leave (Def f []) unchanged even for
          -- -- proj-like funs.
          -- m <- elimView False m
          -- n <- elimView False n
          -- Andreas, 2015-07-01, actually, don't put them into the spine.
          -- Polarity cannot be communicated properly if projection-like
          -- functions are post-fix.
          case (m, n) of
            (Pi{}, Pi{}) -> equalFun m n

            (Sort s1, Sort s2) -> compareSort CmpEq s1 s2

            (Lit l1, Lit l2) | l1 == l2 -> return ()
            (Var i es, Var i' es') | i == i' -> do
                a <- typeOfBV i
                -- Variables are invariant in their arguments
                compareElims [] [] a (var i) es es'

            -- The case of definition application:
            (Def f es, Def f' es') -> do

                -- 1. All absurd lambdas are equal.
                unlessM (bothAbsurd f f') $ do

                -- 2. If the heads are unequal, the only chance is subtyping between SIZE and SIZELT.
                if f /= f' then trySizeUniv cmp t m n f es f' es' else do

                -- 3. If the heads are equal:
                -- 3a. If there are no arguments, we are done.
                unless (null es && null es') $ do

                -- 3b. If some cubical magic kicks in, we are done.
                unlessM (compareEtaPrims f es es') $ do

                -- 3c. Oh no, we actually have to work and compare the eliminations!
                 a <- computeElimHeadType f es es'
                 -- The polarity vector of projection-like functions
                 -- does not include the parameters.
                 pol <- getPolarity' cmp f
                 compareElims pol [] a (Def f []) es es'

            -- Due to eta-expansion, these constructors are fully applied.
            (Con x ci xArgs, Con y _ yArgs)
                | x == y -> do
                    -- Get the type of the constructor instantiated to the datatype parameters.
                    a' <- conType x t
                    forcedArgs <- getForcedArgs $ conName x
                    -- Constructors are covariant in their arguments
                    -- (see test/succeed/CovariantConstructors).
                    compareElims (repeat $ polFromCmp cmp) forcedArgs a' (Con x ci []) xArgs yArgs
            _ -> etaInequal cmp t m n -- fixes issue 856 (unsound conversion error)
    where
        -- returns True in case we handled the comparison already.
        compareEtaPrims :: QName -> Elims -> Elims -> TCM Bool
        compareEtaPrims q es es' = do
          munglue <- getPrimitiveName' builtin_unglue
          msubout <- getPrimitiveName' builtinSubOut
          case () of
            _ | Just q == munglue -> compareUnglueApp q es es'
            _ | Just q == msubout -> compareSubApp q es es'
            _                     -> return False
        compareSubApp q es es' = do
          let (as,bs) = splitAt 5 es; (as',bs') = splitAt 5 es'
          case (allApplyElims as, allApplyElims as') of
            (Just [a,bA,phi,u,x], Just [a',bA',phi',u',x']) -> do
              tSub <- primSub
              -- Andrea, 28-07-16:
              -- comparing the types is most probably wasteful,
              -- since b and b' should be neutral terms, but it's a
              -- precondition for the compareAtom call to make
              -- sense.
              equalType (El Inf $ apply tSub $ [a] ++ map (setHiding NotHidden) [bA,phi,u])
                        (El Inf $ apply tSub $ [a] ++ map (setHiding NotHidden) [bA',phi',u'])
              compareAtom cmp (El Inf $ apply tSub $ [a] ++ map (setHiding NotHidden) [bA,phi,u])
                              (unArg x) (unArg x')
              compareElims [] [] (El (tmSort (unArg a)) (unArg bA)) (Def q as) bs bs'
              return True
            _  -> return False
        compareUnglueApp q es es' = do
          let (as,bs) = splitAt 8 es; (as',bs') = splitAt 8 es'
          case (allApplyElims as, allApplyElims as') of
            (Just [la,lb,bA,phi,bT,f,pf,b], Just [la',lb',bA',phi',bT',f',pf',b']) -> do
              tGlue <- getPrimitiveTerm builtinGlue
              -- Andrea, 28-07-16:
              -- comparing the types is most probably wasteful,
              -- since b and b' should be neutral terms, but it's a
              -- precondition for the compareAtom call to make
              -- sense.
              equalType (El (tmSort (unArg lb)) $ apply tGlue $ [la,lb] ++ map (setHiding NotHidden) [bA,phi,bT,f,pf])
                        (El (tmSort (unArg lb')) $ apply tGlue $ [la',lb'] ++ map (setHiding NotHidden) [bA',phi',bT',f',pf'])
              compareAtom cmp (El (tmSort (unArg lb)) $ apply tGlue $ [la,lb] ++ map (setHiding NotHidden) [bA,phi,bT,f,pf])
                              (unArg b) (unArg b')
              compareElims [] [] (El (tmSort (unArg la)) (unArg bA)) (Def q as) bs bs'
              return True
            _  -> return False
        -- Andreas, 2013-05-15 due to new postponement strategy, type can now be blocked
        conType c t = ifBlockedType t (\ _ _ -> patternViolation) $ \ _ t -> do
          let impossible = do
                reportSDoc "impossible" 10 $
                  "expected data/record type, found " <+> prettyTCM t
                reportSDoc "impossible" 70 $ nest 2 $ "raw =" <+> pretty t
                -- __IMPOSSIBLE__
                -- Andreas, 2013-10-20:  in case termination checking fails
                -- we might get some unreduced types here.
                -- In issue 921, this happens during the final attempt
                -- to solve left-over constraints.
                -- Thus, instead of crashing, just give up gracefully.
                patternViolation
          maybe impossible (return . snd) =<< getFullyAppliedConType c t
        equalFun t1 t2 = case (t1, t2) of
          (Pi dom1 b1, Pi dom2 b2) -> do
            verboseBracket "tc.conv.fun" 15 "compare function types" $ do
              reportSDoc "tc.conv.fun" 20 $ nest 2 $ vcat
                [ "t1 =" <+> prettyTCM t1
                , "t2 =" <+> prettyTCM t2 ]
              compareDom cmp dom2 dom1 b1 b2 errH errR $
                compareType cmp (absBody b1) (absBody b2)
            where
            errH = typeError $ UnequalHiding t1 t2
            errR = typeError $ UnequalRelevance cmp t1 t2
          _ -> __IMPOSSIBLE__

-- | Check whether @a1 `cmp` a2@ and continue in context extended by @a1@.
compareDom :: Free c
  => Comparison -- ^ @cmp@ The comparison direction
  -> Dom Type   -- ^ @a1@  The smaller domain.
  -> Dom Type   -- ^ @a2@  The other domain.
  -> Abs b      -- ^ @b1@  The smaller codomain.
  -> Abs c      -- ^ @b2@  The bigger codomain.
  -> TCM ()     -- ^ Continuation if mismatch in 'Hiding'.
  -> TCM ()     -- ^ Continuation if mismatch in 'Relevance'.
  -> TCM ()     -- ^ Continuation if comparison is successful.
  -> TCM ()
compareDom cmp dom1@(Dom{domInfo = i1, unDom = a1}) dom2@(Dom{domInfo = i2, unDom = a2}) b1 b2 errH errR cont
  | not (sameHiding dom1 dom2) = errH
  | not $ compareRelevance cmp (getRelevance dom1) (getRelevance dom2) = errR
  | otherwise = do
      let r = max (getRelevance dom1) (getRelevance dom2)
              -- take "most irrelevant"
          dependent = (r /= Irrelevant) && isBinderUsed b2
      pid <- newProblem_ $ compareType cmp a1 a2
      dom <- if dependent
             then (\ a -> dom1 {unDom = a}) <$> blockTypeOnProblem a1 pid
             else return dom1
        -- We only need to require a1 == a2 if b2 is dependent
        -- If it's non-dependent it doesn't matter what we add to the context.
      name <- freshName_ $ suggest b1 b2
      addContext (name, dom) $ cont
      stealConstraints pid
        -- Andreas, 2013-05-15 Now, comparison of codomains is not
        -- blocked any more by getting stuck on domains.
        -- Only the domain type in context will be blocked.
        -- But see issue #1258.

compareRelevance :: Comparison -> Relevance -> Relevance -> Bool
compareRelevance CmpEq  = (==)
compareRelevance CmpLeq = (<=)

-- | When comparing argument spines (in compareElims) where the first arguments
--   don't match, we keep going, substituting the anti-unification of the two
--   terms in the telescope. More precisely:
--
--  @@
--    (u = v : A)[pid]   w = antiUnify pid A u v   us = vs : Δ[w/x]
--    -------------------------------------------------------------
--                    u us = v vs : (x : A) Δ
--  @@
--
--   The simplest case of anti-unification is to return a fresh metavariable
--   (created by blockTermOnProblem), but if there's shared structure between
--   the two terms we can expose that.
--
--   This is really a crutch that lets us get away with things that otherwise
--   would require heterogenous conversion checking. See for instance issue
--   #2384.
antiUnify :: ProblemId -> Type -> Term -> Term -> TCM Term
antiUnify pid a u v = do
  ((u, v), eq) <- SynEq.checkSyntacticEquality u v
  if eq then return u else do
  (u, v) <- reduce (u, v)
  case (u, v) of
    (Pi ua ub, Pi va vb) -> do
      wa0 <- antiUnifyType pid (unDom ua) (unDom va)
      let wa = wa0 <$ ua
      wb <- addContext wa $ antiUnifyType pid (unAbs ub) (unAbs vb)
      return $ Pi wa (wb <$ ub)
    (Lam i u, Lam _ v) ->
      case unEl a of
        Pi a b -> Lam i . (<$ u) <$> addContext a (antiUnify pid (unAbs b) (unAbs u) (unAbs v))
        _      -> fallback
    (Var i us, Var j vs) | i == j -> maybeGiveUp $ do
      a <- typeOfBV i
      antiUnifyElims pid a (var i) us vs
    -- Andreas, 2017-07-27:
    -- It seems that nothing guarantees here that the constructors are fully
    -- applied!?  Thus, @a@ could be a function type and we need the robust
    -- @getConType@ here.
    -- (Note that @patternViolation@ swallows exceptions coming from @getConType@
    -- thus, we would not see clearly if we used @getFullyAppliedConType@ instead.)
    (Con x ci us, Con y _ vs) | x == y -> maybeGiveUp $ do
      a <- maybe patternViolation (return . snd) =<< getConType x a
      antiUnifyElims pid a (Con x ci []) us vs
    (Def f us, Def g vs) | f == g, length us == length vs -> maybeGiveUp $ do
      a <- computeElimHeadType f us vs
      antiUnifyElims pid a (Def f []) us vs
    _ -> fallback
  where
    fallback = blockTermOnProblem a u pid
    maybeGiveUp m = m `catchError_` \ err ->
      case err of
        PatternErr{} -> fallback
        _            -> throwError err

antiUnifyType :: ProblemId -> Type -> Type -> TCM Type
antiUnifyType pid (El s a) (El _ b) = El s <$> antiUnify pid (sort s) a b

antiUnifyElims :: ProblemId -> Type -> Term -> Elims -> Elims -> TCM Term
antiUnifyElims pid a self [] [] = return self
antiUnifyElims pid a self (Proj o f : es1) (Proj _ g : es2) | f == g = do
  res <- projectTyped self a o f
  case res of
    Just (_, self, a) -> antiUnifyElims pid a self es1 es2
    Nothing -> patternViolation -- can fail for projection like
antiUnifyElims pid a self (Apply u : es1) (Apply v : es2) = do
  case unEl a of
    Pi a b -> do
      w <- antiUnify pid (unDom a) (unArg u) (unArg v)
      antiUnifyElims pid (b `lazyAbsApp` w) (apply self [w <$ u]) es1 es2
    _ -> patternViolation
antiUnifyElims _ _ _ _ _ = patternViolation -- trigger maybeGiveUp in antiUnify

-- | @compareElims pols a v els1 els2@ performs type-directed equality on eliminator spines.
--   @t@ is the type of the head @v@.
compareElims :: [Polarity] -> [IsForced] -> Type -> Term -> [Elim] -> [Elim] -> TCM ()
compareElims pols0 fors0 a v els01 els02 = catchConstraint (ElimCmp pols0 fors0 a v els01 els02) $ do
  let v1 = applyE v els01
      v2 = applyE v els02
      failure = typeError $ UnequalTerms CmpEq v1 v2 a
        -- Andreas, 2013-03-15 since one of the spines is empty, @a@
        -- is the correct type here.
  unless (null els01) $ do
    reportSDoc "tc.conv.elim" 25 $ "compareElims" $$ do
     nest 2 $ vcat
      [ "a     =" <+> prettyTCM a
      , "pols0 (truncated to 10) =" <+> sep (map prettyTCM $ take 10 pols0)
      , "fors0 (truncated to 10) =" <+> sep (map prettyTCM $ take 10 fors0)
      , "v     =" <+> prettyTCM v
      , "els01 =" <+> prettyTCM els01
      , "els02 =" <+> prettyTCM els02
      ]
  case (els01, els02) of
    ([]         , []         ) -> return ()
    ([]         , Proj{}:_   ) -> failure -- not impossible, see issue 821
    (Proj{}  : _, []         ) -> failure -- could be x.p =?= x for projection p
    ([]         , Apply{} : _) -> failure -- not impossible, see issue 878
    (Apply{} : _, []         ) -> failure
    ([]         , IApply{} : _) -> failure
    (IApply{} : _, []         ) -> failure
    (Apply{} : _, Proj{}  : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True -- NB: popped up in issue 889
    (Proj{}  : _, Apply{} : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True -- but should be impossible (but again in issue 1467)
    (IApply{} : _, Proj{}  : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True
    (Proj{}  : _, IApply{} : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True
    (IApply{} : _, Apply{}  : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True
    (Apply{}  : _, IApply{} : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True
    (e@(IApply x1 y1 r1) : els1, IApply x2 y2 r2 : els2) -> do
      reportSDoc "tc.conv.elim" 25 $ "compareElims IApply"
       -- Andrea: copying stuff from the Apply case..
      let (pol, pols) = nextPolarity pols0
      ifBlockedType a (\ m t -> patternViolation) $ \ _ a -> do
          va <- pathView a
          reportSDoc "tc.conv.elim.iapply" 60 $ "compareElims IApply" $$ do
            nest 2 $ "va =" <+> text (show (isPathType va))
          case va of
            PathType s path l bA x y -> do
              b <- elInf primInterval
              compareWithPol pol (flip compareTerm b)
                                  r1 r2
              -- TODO: compare (x1,x2) and (y1,y2) ?
              let r = r1 -- TODO Andrea:  do blocking
              codom <- el' (pure . unArg $ l) ((pure . unArg $ bA) <@> pure r)
              compareElims pols [] codom -- Path non-dependent (codom `lazyAbsApp` unArg arg)
                                (applyE v [e]) els1 els2
            -- We allow for functions (i : I) -> ... to also be heads of a IApply,
            -- because @etaContract@ can produce such terms
            OType t@(El _ Pi{}) -> compareElims pols0 fors0 t v (Apply (defaultArg r1) : els1) (Apply (defaultArg r2) : els2)

            OType{} -> patternViolation

    (Apply arg1 : els1, Apply arg2 : els2) ->
      verboseBracket "tc.conv.elim" 20 "compare Apply" $ do
      reportSDoc "tc.conv.elim" 10 $ nest 2 $ vcat
        [ "a    =" <+> prettyTCM a
        , "v    =" <+> prettyTCM v
        , "arg1 =" <+> prettyTCM arg1
        , "arg2 =" <+> prettyTCM arg2
        ]
      reportSDoc "tc.conv.elim" 50 $ nest 2 $ vcat
        [ "v    =" <+> pretty v
        , "arg1 =" <+> pretty arg1
        , "arg2 =" <+> pretty arg2
        , ""
        ]
      let (pol, pols) = nextPolarity pols0
          (for, fors) = nextIsForced fors0
      ifBlockedType a (\ m t -> patternViolation) $ \ _ a -> do
        case unEl a of
          (Pi (Dom{domInfo = info, unDom = b}) codom) -> do
            mlvl <- tryMaybe primLevel
            let freeInCoDom (Abs _ c) = 0 `freeInIgnoringSorts` c
                freeInCoDom _         = False
                dependent = (Just (unEl b) /= mlvl) && freeInCoDom codom
                  -- Level-polymorphism (x : Level) -> ... does not count as dependency here
                     -- NB: we could drop the free variable test and still be sound.
                     -- It is a trade-off between the administrative effort of
                     -- creating a blocking and traversing a term for free variables.
                     -- Apparently, it is believed that checking free vars is cheaper.
                     -- Andreas, 2013-05-15
                r = getRelevance info

-- NEW, Andreas, 2013-05-15

            -- compare arg1 and arg2
            pid <- newProblem_ $ applyRelevanceToContext r $
                if isForced for then
                  return ()
                else if isIrrelevant r then
                  compareIrrelevant b (unArg arg1) (unArg arg2)
                else
                  compareWithPol pol (flip compareTerm b)
                    (unArg arg1) (unArg arg2)
            -- if comparison got stuck and function type is dependent, block arg
            solved <- isProblemSolved pid
            arg <- if dependent && not solved
                   then do
                    arg <- (arg1 $>) <$> antiUnify pid b (unArg arg1) (unArg arg2)
                    reportSDoc "tc.conv.elims" 30 $ hang "Anti-unification:" 2 (prettyTCM arg)
                    reportSDoc "tc.conv.elims" 70 $ nest 2 $ "raw:" <+> pretty arg
                    return arg
                   else return arg1
            -- continue, possibly with blocked instantiation
            compareElims pols fors (codom `lazyAbsApp` unArg arg) (apply v [arg]) els1 els2
            -- any left over constraints of arg are associatd to the comparison
            stealConstraints pid
            {- Stealing solves this issue:

               Does not create enough blocked tc-problems,
               see test/fail/DontPrune.
               (There are remaining problems which do not show up as yellow.)
               Need to find a way to associate pid also to result of compareElims.
            -}
          a -> do
            reportSDoc "impossible" 10 $
              "unexpected type when comparing apply eliminations " <+> prettyTCM a
            reportSDoc "impossible" 50 $ "raw type:" <+> pretty a
            patternViolation
            -- Andreas, 2013-10-22
            -- in case of disabled reductions (due to failing termination check)
            -- we might get stuck, so do not crash, but fail gently.
            -- __IMPOSSIBLE__

    -- case: f == f' are projections
    (Proj o f : els1, Proj _ f' : els2)
      | f /= f'   -> typeError . GenericError . show =<< prettyTCM f <+> "/=" <+> prettyTCM f'
      | otherwise -> ifBlockedType a (\ m t -> patternViolation) $ \ _ a -> do
        res <- projectTyped v a o f -- fails only if f is proj.like but parameters cannot be retrieved
        case res of
          Just (_, u, t) -> do
            -- Andreas, 2015-07-01:
            -- The arguments following the principal argument of a projection
            -- are invariant.  (At least as long as we have no explicit polarity
            -- annotations.)
            compareElims [] [] t u els1 els2
          Nothing -> do
            reportSDoc "tc.conv.elims" 30 $ sep
              [ text $ "projection " ++ show f
              , text   "applied to value " <+> prettyTCM v
              , text   "of unexpected type " <+> prettyTCM a
              ]
            patternViolation


-- | "Compare" two terms in irrelevant position.  This always succeeds.
--   However, we can dig for solutions of irrelevant metas in the
--   terms we compare.
--   (Certainly not the systematic solution, that'd be proof search...)
compareIrrelevant :: Type -> Term -> Term -> TCM ()
{- 2012-04-02 DontCare no longer present
compareIrrelevant t (DontCare v) w = compareIrrelevant t v w
compareIrrelevant t v (DontCare w) = compareIrrelevant t v w
-}
compareIrrelevant t v w = do
  reportSDoc "tc.conv.irr" 20 $ vcat
    [ "compareIrrelevant"
    , nest 2 $ "v =" <+> prettyTCM v
    , nest 2 $ "w =" <+> prettyTCM w
    ]
  reportSDoc "tc.conv.irr" 50 $ vcat
    [ nest 2 $ "v =" <+> pretty v
    , nest 2 $ "w =" <+> pretty w
    ]
  try v w $ try w v $ return ()
  where
    try (MetaV x es) w fallback = do
      mv <- lookupMeta x
      let rel  = getMetaRelevance mv
          inst = case mvInstantiation mv of
                   InstV{} -> True
                   _       -> False
      reportSDoc "tc.conv.irr" 20 $ vcat
        [ nest 2 $ text $ "rel  = " ++ show rel
        , nest 2 $ "inst =" <+> pretty inst
        ]
      if not (isIrrelevant rel) || inst
        then fallback
        -- Andreas, 2016-08-08, issue #2131:
        -- Mining for solutions for irrelevant metas is not definite.
        -- Thus, in case of error, leave meta unsolved.
        else (assignE DirEq x es w $ compareIrrelevant t) `catchError` \ _ -> fallback
        -- the value of irrelevant or unused meta does not matter
    try v w fallback = fallback

compareWithPol :: Polarity -> (Comparison -> a -> a -> TCM ()) -> a -> a -> TCM ()
compareWithPol Invariant     cmp x y = cmp CmpEq x y
compareWithPol Covariant     cmp x y = cmp CmpLeq x y
compareWithPol Contravariant cmp x y = cmp CmpLeq y x
compareWithPol Nonvariant    cmp x y = return ()

polFromCmp :: Comparison -> Polarity
polFromCmp CmpLeq = Covariant
polFromCmp CmpEq  = Invariant

-- | Type-directed equality on argument lists
--
compareArgs :: [Polarity] -> [IsForced] -> Type -> Term -> Args -> Args -> TCM ()
compareArgs pol for a v args1 args2 =
  compareElims pol for a v (map Apply args1) (map Apply args2)

---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | Equality on Types
compareType :: Comparison -> Type -> Type -> TCM ()
compareType cmp ty1@(El s1 a1) ty2@(El s2 a2) =
    verboseBracket "tc.conv.type" 20 "compareType" $
    catchConstraint (TypeCmp cmp ty1 ty2) $ do
        reportSDoc "tc.conv.type" 50 $ vcat
          [ "compareType" <+> sep [ prettyTCM ty1 <+> prettyTCM cmp
                                       , prettyTCM ty2 ]
          , hsep [ "   sorts:", prettyTCM s1, " and ", prettyTCM s2 ]
          ]
-- Andreas, 2011-4-27 should not compare sorts, but currently this is needed
-- for solving sort and level metas
        compareSort CmpEq s1 s2 `catchError` \err -> case err of
          TypeError _ e -> do
            reportSDoc "tc.conv.type" 30 $ vcat
              [ "sort comparison failed"
              , nest 2 $ vcat
                [ "s1 =" <+> prettyTCM s1
                , "s2 =" <+> prettyTCM s2
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
            -- Andreas, 2013-10-31 Maybe the error went away
            -- when we compared the types.  So we try the sort comparison
            -- again, this time not catching the error.  (see Issue 930)
            -- throwError err
            compareSort CmpEq s1 s2
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
--
--   Precondition: @a@ and @b@ are reduced.
coerce :: Comparison -> Term -> Type -> Type -> TCM Term
coerce cmp v t1 t2 = blockTerm t2 $ do
  verboseS "tc.conv.coerce" 10 $ do
    (a1,a2) <- reify (t1,t2)
    let dbglvl = if isSet a1 && isSet a2 then 50 else 10
    reportSDoc "tc.conv.coerce" dbglvl $
      "coerce" <+> vcat
        [ "term      v  =" <+> prettyTCM v
        , "from type t1 =" <+> prettyTCM a1
        , "to type   t2 =" <+> prettyTCM a2
        , "comparison   =" <+> prettyTCM cmp
        ]
    reportSDoc "tc.conv.coerce" 70 $
      "coerce" <+> vcat
        [ "term      v  =" <+> pretty v
        , "from type t1 =" <+> pretty t1
        , "to type   t2 =" <+> pretty t2
        , "comparison   =" <+> pretty cmp
        ]
  -- v <$ do workOnTypes $ leqType t1 t2
  -- take off hidden/instance domains from t1 and t2
  TelV tel1 b1 <- telViewUpTo' (-1) notVisible t1
  TelV tel2 b2 <- telViewUpTo' (-1) notVisible t2
  let n = size tel1 - size tel2
  -- the crude solution would be
  --   v' = λ {tel2} → v {tel1}
  -- however, that may introduce unneccessary many function types
  -- If n  > 0 and b2 is not blocked, it is safe to
  -- insert n many hidden args
  if n <= 0 then fallback else do
    ifBlockedType b2 (\ _ _ -> fallback) $ \ _ _ -> do
      (args, t1') <- implicitArgs n notVisible t1
      let v' = v `apply` args
      v' <$ coerceSize (compareType cmp) v' t1' t2
  where
    fallback = v <$ coerceSize (compareType cmp) v t1 t2

-- | Account for situations like @k : (Size< j) <= (Size< k + 1)@
--
--   Actually, the semantics is
--   @(Size<= k) ∩ (Size< j) ⊆ rhs@
--   which gives a disjunctive constraint.  Mmmh, looks like stuff
--   TODO.
--
--   For now, we do a cheap heuristics.
--
--   Precondition: types are reduced.
coerceSize :: (Type -> Type -> TCM ()) -> Term -> Type -> Type -> TCM ()
coerceSize leqType v t1 t2 = workOnTypes $ do
    reportSDoc "tc.conv.coerce" 70 $
      "coerceSize" <+> vcat
        [ "term      v  =" <+> pretty v
        , "from type t1 =" <+> pretty t1
        , "to type   t2 =" <+> pretty t2
        ]
    let fallback = leqType t1 t2
        done = caseMaybeM (isSizeType t1) fallback $ \ _ -> return ()
    -- Andreas, 2015-07-22, Issue 1615:
    -- If t1 is a meta and t2 a type like Size< v2, we need to make sure we do not miss
    -- the constraint v < v2!
    caseMaybeM (isSizeType t2) fallback $ \ b2 -> do
      -- Andreas, 2017-01-20, issue #2329:
      -- If v is not a size suitable for the solver, like a neutral term,
      -- we can only rely on the type.
      mv <- sizeMaxView v
      if any (\case{ DOtherSize{} -> True; _ -> False }) mv then fallback else do
      -- Andreas, 2015-02-11 do not instantiate metas here (triggers issue 1203).
      unlessM (tryConversion $ dontAssignMetas $ leqType t1 t2) $ do
        -- A (most probably weaker) alternative is to just check syn.eq.
        -- ifM (snd <$> checkSyntacticEquality t1 t2) (return v) $ {- else -} do
        reportSDoc "tc.conv.coerce" 20 $ "coercing to a size type"
        case b2 of
          -- @t2 = Size@.  We are done!
          BoundedNo -> done
          -- @t2 = Size< v2@
          BoundedLt v2 -> do
            sv2 <- sizeView v2
            case sv2 of
              SizeInf     -> done
              OtherSize{} -> do
                -- Andreas, 2014-06-16:
                -- Issue 1203: For now, just treat v < v2 as suc v <= v2
                -- TODO: Need proper < comparison
                vinc <- sizeSuc 1 v
                compareSizes CmpLeq vinc v2
                done
              -- @v2 = a2 + 1@: In this case, we can try @v <= a2@
              SizeSuc a2 -> do
                compareSizes CmpLeq v a2
                done  -- to pass Issue 1136

---------------------------------------------------------------------------
-- * Sorts and levels
---------------------------------------------------------------------------

compareLevel :: Comparison -> Level -> Level -> TCM ()
compareLevel CmpLeq u v = leqLevel u v
compareLevel CmpEq  u v = equalLevel u v

compareSort :: Comparison -> Sort -> Sort -> TCM ()
compareSort CmpEq  = equalSort
compareSort CmpLeq = leqSort

-- | Check that the first sort is less or equal to the second.
--
--   We can put @SizeUniv@ below @Inf@, but otherwise, it is
--   unrelated to the other universes.
--
leqSort :: Sort -> Sort -> TCM ()
leqSort s1 s2 = catchConstraint (SortCmp CmpLeq s1 s2) $ do
  (s1,s2) <- reduce (s1,s2)
  let postpone = addConstraint (SortCmp CmpLeq s1 s2)
      no       = typeError $ NotLeqSort s1 s2
      yes      = return ()
  reportSDoc "tc.conv.sort" 30 $
    sep [ "leqSort"
        , nest 2 $ fsep [ prettyTCM s1 <+> "=<"
                        , prettyTCM s2 ]
        ]
  propEnabled <- isPropEnabled

  let fvsRHS = IntSet.toList $ allFreeVars s2
  badRigid <- s1 `rigidVarsNotContainedIn` fvsRHS

  case (s1, s2) of
      -- Andreas, 2018-09-03: crash on dummy sort
      (DummyS s, _) -> impossibleSort s
      (_, DummyS s) -> impossibleSort s

      -- The most basic rule: @Set l =< Set l'@ iff @l =< l'@
      (Type a  , Type b  ) -> leqLevel a b

      -- Likewise for @Prop@
      (Prop a  , Prop b  ) -> leqLevel a b

      -- @Prop l@ is below @Set l@
      (Prop a  , Type b  ) -> leqLevel a b
      (Type a  , Prop b  ) -> no

      -- Setω is the top sort
      (_       , Inf     ) -> yes
      (Inf     , _       ) -> equalSort s1 s2

      -- @SizeUniv@ and @Prop0@ are bottom sorts.
      -- So is @Set0@ if @Prop@ is not enabled.
      (_       , SizeUniv) -> equalSort s1 s2
      (_       , Prop (Max [])) -> equalSort s1 s2
      (_       , Type (Max []))
        | not propEnabled  -> equalSort s1 s2

      -- SizeUniv is unrelated to any @Set l@ or @Prop l@
      (SizeUniv, Type{}  ) -> no
      (SizeUniv, Prop{}  ) -> no

      -- If the first sort rigidly depends on a variable and the second
      -- sort does not mention this variable, the second sort must be Inf.
      (_       , _       ) | badRigid -> equalSort s2 Inf

      -- This shouldn't be necessary
      (UnivSort Inf , UnivSort Inf) -> yes

      -- PiSort, UnivSort and MetaS might reduce once we instantiate
      -- more metas, so we postpone.
      (PiSort{}, _       ) -> postpone
      (_       , PiSort{}) -> postpone
      (UnivSort{}, _     ) -> postpone
      (_     , UnivSort{}) -> postpone
      (MetaS{} , _       ) -> postpone
      (_       , MetaS{} ) -> postpone

  where
  impossibleSort s = do
    reportSLn "impossible" 10 $ unlines
      [ "leqSort: found dummy sort with description:"
      , s
      ]
    __IMPOSSIBLE__

leqLevel :: Level -> Level -> TCM ()
leqLevel a b = liftTCM $ do
  reportSDoc "tc.conv.nat" 30 $
    "compareLevel" <+>
      sep [ prettyTCM a <+> "=<"
          , prettyTCM b ]
  -- Andreas, 2015-12-28 Issue 1757
  -- We normalize both sides to make the syntactic equality check (==) stronger.
  -- See case for `same term` below.
  a <- normalise a
  b <- normalise b
  leqView a b
  where
    -- Andreas, 2016-09-28
    -- If we have to postpone a constraint, then its simplified form!
    leqView a@(Max as) b@(Max bs) = catchConstraint (LevelCmp CmpLeq a b) $ do
      reportSDoc "tc.conv.nat" 30 $
        "compareLevelView" <+>
          sep [ pretty a <+> "=<"
              , pretty b ]
      wrap $ case (as, bs) of

        -- same term
        _ | as == bs -> ok

        -- 0 ≤ any
        ([], _) -> ok

        -- as ≤ 0
        (as, [])              -> sequence_ [ equalLevel' (Max [a]) (Max []) | a <- as ]
        (as, [ClosedLevel 0]) -> sequence_ [ equalLevel' (Max [a]) (Max []) | a <- as ]
           -- Andreas, 2016-09-28, @[ClosedLevel 0]@ is possible if we come from case
           -- "reduce constants" where we run @subtr@ on both sides.
           -- See test/Succeed/LevelMetaLeqZero.agda.

        -- as ≤ [b]
        (as@(_:_:_), [b]) -> sequence_ [ leqView (Max [a]) (Max [b]) | a <- as ]

        -- reduce constants
        (as, bs) | minN > 0 -> leqView (Max $ map (subtr minN) as) (Max $ map (subtr minN) bs)
          where
            ns = map constant as
            ms = map constant bs
            minN = minimum (ns ++ ms)

        -- remove subsumed
        -- Andreas, 2014-04-07: This is ok if we do not go back to equalLevel
        (as, bs)
          | not $ null subsumed -> leqView (Max $ as List.\\ subsumed) (Max bs)
          where
            subsumed = [ a | a@(Plus m l) <- as, n <- findN l, m <= n ]
            -- @findN a@ finds the unique(?) term @Plus n a@ in @bs@, if any.
            -- Andreas, 2014-04-07 Why must there be a unique term?
            findN a = case [ n | Plus n b <- bs, b == a ] of
                        [n] -> [n]
                        _   -> []

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

        -- Andreas, 2016-09-28: This simplification loses the solution lzero.
        -- Thus, it is invalid.
        -- See test/Succeed/LevelMetaLeqNeutralLevel.agda.
        -- -- [a] ≤ [neutral]
        -- ([a@(Plus n _)], [b@(Plus m NeutralLevel{})])
        --   | m == n -> equalLevel' (Max [a]) (Max [b])
        --   -- Andreas, 2014-04-07: This call to equalLevel is ok even if we removed
        --   -- subsumed terms from the lhs.

        -- anything else
        _ -> postpone
      where
        ok       = return ()
        notok    = unlessM typeInType $ typeError $ NotLeqSort (Type a) (Type b)
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

        unneutral (Plus _ (NeutralLevel _ v)) = v
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
  -- Andreas, 2013-10-31 Use normalization to make syntactic equality stronger
  (a, b) <- normalise (a, b)
  equalLevel' a b

-- | Precondition: levels are 'normalise'd.
equalLevel' :: Level -> Level -> TCM ()
equalLevel' a b = do
  reportSDoc "tc.conv.level" 50 $ sep [ "equalLevel", nest 2 $ parens $ pretty a, nest 2 $ parens $ pretty b ]
  liftTCM $ catchConstraint (LevelCmp CmpEq a b) $
    check a b
  where
    check a@(Max as) b@(Max bs) = do
      -- Jesper, 2014-02-02 remove terms that certainly do not contribute
      -- to the maximum
      as <- return $ [ a | a <- as, not $ a `isStrictlySubsumedBy` bs ]
      bs <- return $ [ b | b <- bs, not $ b `isStrictlySubsumedBy` as ]
      -- Andreas, 2013-10-31 remove common terms (that don't contain metas!!)
      -- THAT's actually UNSOUND when metas are instantiated, because
      --     max a b == max a c  does not imply  b == c
      -- as <- return $ Set.fromList $ closed0 as
      -- bs <- return $ Set.fromList $ closed0 bs
      -- let cs = Set.filter (not . hasMeta) $ Set.intersection as bs
      -- as <- return $ Set.toList $ as Set.\\ cs
      -- bs <- return $ Set.toList $ bs Set.\\ cs
      as <- return $ List.sort $ closed0 as
      bs <- return $ List.sort $ closed0 bs
      reportSDoc "tc.conv.level" 40 $
        sep [ "equalLevel"
            , vcat [ nest 2 $ sep [ prettyTCM a <+> "=="
                                  , prettyTCM b
                                  ]
                   , "reduced"
                   , nest 2 $ sep [ prettyTCM (Max as) <+> "=="
                                  , prettyTCM (Max bs)
                                  ]
                   ]
            ]
      reportSDoc "tc.conv.level" 50 $
        sep [ text "equalLevel"
            , vcat [ nest 2 $ sep [ pretty (Max as) <+> "=="
                                  , pretty (Max bs)
                                  ]
                   ]
            ]
      case (as, bs) of
        _ | as == bs -> ok
          | any isBlocked (as ++ bs) -> do
              lvl <- levelType
              liftTCM $ addConstraint $ ValueCmp CmpEq lvl (Level a) (Level b)

        -- closed == closed
        ([ClosedLevel n], [ClosedLevel m])
          | n == m    -> ok
          | otherwise -> notok

        -- closed == neutral
        ([ClosedLevel{}], _) | any isNeutral bs -> notok
        (_, [ClosedLevel{}]) | any isNeutral as -> notok

        -- 0 == any
        ([ClosedLevel 0], bs@(_:_:_)) -> sequence_ [ equalLevel' (Max []) (Max [b]) | b <- bs ]
        (as@(_:_:_), [ClosedLevel 0]) -> sequence_ [ equalLevel' (Max [a]) (Max []) | a <- as ]
        -- Andreas, 2014-04-07 Why should the following be ok?
        --   X (suc a)  could be different from  X (suc (suc a))
        -- -- Same meta
        -- ([Plus n (MetaLevel x _)], [Plus m (MetaLevel y _)])
        --   | n == m && x == y -> ok

        -- meta == any
        ([Plus n (MetaLevel x as)], _)
          | any (isThisMeta x) bs -> postpone
        (_, [Plus n (MetaLevel x bs)])
          | any (isThisMeta x) as -> postpone
        ([Plus n (MetaLevel x as')], [Plus m (MetaLevel y bs')])
            -- lexicographic comparison intended!
          | (n, y) < (m, x)            -> meta n x as' bs
          | otherwise                  -> meta m y bs' as
        ([Plus n (MetaLevel x as')],_) -> meta n x as' bs
        (_,[Plus m (MetaLevel y bs')]) -> meta m y bs' as

        -- any other metas
        -- Andreas, 2013-10-31: There could be metas in neutral levels (see Issue 930).
        -- Should not we postpone there as well?  Yes!
        _ | any hasMeta (as ++ bs) -> postpone

        -- neutral/closed == neutral/closed
        _ | all isNeutralOrClosed (as ++ bs) -> do
          reportSLn "tc.conv.level" 60 $ "equalLevel: all are neutral or closed"
          if length as == length bs
            then zipWithM_ (\a b -> [a] =!= [b]) as bs
            else notok

        -- more cases?
        _ -> postpone

      where
        a === b   = unlessM typeInType $ do
            lvl <- levelType
            equalAtom lvl a b
        as =!= bs = levelTm (Max as) === levelTm (Max bs)

        ok       = return ()
        notok    = unlessM typeInType notOk
        notOk    = typeError $ UnequalSorts (Type a) (Type b)
        postpone = do
          reportSDoc "tc.conv.level" 30 $ hang "postponing:" 2 $ hang (pretty a <+> "==") 0 (pretty b)
          patternViolation

        closed0 [] = [ClosedLevel 0]
        closed0 as = as

        -- perform assignment (Plus n (MetaLevel x as)) := bs
        meta n x as bs = do
          reportSLn "tc.meta.level" 30 $ "Assigning meta level"
          reportSDoc "tc.meta.level" 50 $ "meta" <+> sep [prettyList $ map pretty as, prettyList $ map pretty bs]
          bs' <- mapM (subtr n) bs
          assignE DirEq x as (levelTm (Max bs')) (===) -- fallback: check equality as atoms

        -- Make sure to give a sensible error message
        wrap m = m `catchError` \err ->
          case err of
            TypeError{} -> notok
            _           -> throwError err

        subtr n (ClosedLevel m)
          | m >= n    = return $ ClosedLevel (m - n)
          | otherwise = ifM typeInType (return $ ClosedLevel 0) $ notOk
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
        isBlocked _                       = False

        hasMeta ClosedLevel{}               = False
        hasMeta (Plus _ MetaLevel{})        = True
        hasMeta (Plus _ (BlockedLevel _ v)) = not $ null $ allMetas v
        hasMeta (Plus _ (NeutralLevel _ v)) = not $ null $ allMetas v
        hasMeta (Plus _ (UnreducedLevel v)) = not $ null $ allMetas v

        isThisMeta x (Plus _ (MetaLevel y _)) = x == y
        isThisMeta _ _                      = False

        constant (ClosedLevel n) = n
        constant (Plus n _)      = n

        (ClosedLevel m) `isStrictlySubsumedBy` [] = m == 0
        (ClosedLevel m) `isStrictlySubsumedBy` ys = m < maximum (map constant ys)
        (Plus m x)      `isStrictlySubsumedBy` ys = not $ null $
          [ n | Plus n y <- ys, x == y, m < n ]


-- | Check that the first sort equal to the second.
equalSort :: Sort -> Sort -> TCM ()
equalSort s1 s2 = do
    catchConstraint (SortCmp CmpEq s1 s2) $ do
        (s1,s2) <- reduce (s1,s2)
        let postpone = addConstraint (SortCmp CmpEq s1 s2)
            yes      = return ()
            no       = unlessM typeInType $ typeError $ UnequalSorts s1 s2
            synEq    = ifNotM (optSyntacticEquality <$> pragmaOptions) postpone $ do
              ((s1,s2) , equal) <- SynEq.checkSyntacticEquality s1 s2
              if | equal     -> yes
                 | otherwise -> postpone

        reportSDoc "tc.conv.sort" 30 $ sep
          [ "equalSort"
          , vcat [ nest 2 $ fsep [ prettyTCM s1 <+> "=="
                                 , prettyTCM s2 ]
                 , nest 2 $ fsep [ pretty s1 <+> "=="
                                 , pretty s2 ]
                 ]
          ]

        propEnabled <- isPropEnabled

        case (s1, s2) of

            -- Andreas, 2018-09-03: crash on dummy sort
            (DummyS s, _) -> impossibleSort s
            (_, DummyS s) -> impossibleSort s

            -- one side is a meta sort: try to instantiate
            -- In case both sides are meta sorts, instantiate the
            -- bigger (i.e. more recent) one.
            (MetaS x es , MetaS y es')
              | x == y                 -> synEq
              | x < y                  -> meta y es' s1
              | otherwise              -> meta x es s2
            (MetaS x es , _          ) -> meta x es s2
            (_          , MetaS x es ) -> meta x es s1

            -- Other blocked sorts: check syntactic equality
            (PiSort{}    , PiSort{}   ) -> synEq
            (UnivSort{}  , UnivSort{} ) -> synEq

            -- diagonal cases for rigid sorts
            (Type a     , Type b     ) -> equalLevel a b
            (SizeUniv   , SizeUniv   ) -> yes
            (Prop a     , Prop b     ) -> equalLevel a b
            (Inf        , Inf        ) -> yes

            -- if @PiSort a b == Set0@, then @b == Set0@
            -- we use this fact to solve metas in @b@,
            -- hopefully allowing the @PiSort@ to reduce.
            (Type (Max []) , PiSort a b   )
              | not propEnabled             -> piSortEqualsBottom set0 a b
            (PiSort a b    , Type (Max []))
              | not propEnabled             -> piSortEqualsBottom set0 a b

            (Prop (Max []) , PiSort a b   ) -> piSortEqualsBottom prop0 a b
            (PiSort a b    , Prop (Max [])) -> piSortEqualsBottom prop0 a b

            -- @PiSort a b == SizeUniv@ iff @b == SizeUniv@
            (SizeUniv   , PiSort a b ) ->
              underAbstraction_ b $ equalSort SizeUniv
            (PiSort a b , SizeUniv   ) ->
              underAbstraction_ b $ equalSort SizeUniv

            -- @Prop0@ and @SizeUniv@ don't contain any universes,
            -- so they cannot be a UnivSort
            (Prop (Max []) , UnivSort s )   -> no
            (UnivSort s    , Prop (Max [])) -> no
            (SizeUniv      , UnivSort s )   -> no
            (UnivSort s    , SizeUniv   )   -> no


            -- PiSort and UnivSort could compute later, so we postpone
            (PiSort{}   , _          ) -> postpone
            (_          , PiSort{}   ) -> postpone
            (UnivSort{} , _          ) -> postpone
            (_          , UnivSort{} ) -> postpone

            -- any other combinations of sorts are not equal
            (_          , _          ) -> no

    where
      -- perform assignment (MetaS x es) := s
      meta x es s = do
        reportSLn "tc.meta.sort" 30 $ "Assigning meta sort"
        reportSDoc "tc.meta.sort" 50 $ "meta" <+> sep [pretty x, prettyList $ map pretty es, pretty s]
        assignE DirEq x es (Sort s) __IMPOSSIBLE__

      set0 = Type $ Max []
      prop0 = Prop $ Max []

      -- equate @piSort a b@ to @s0@, which is assumed to be a (closed) bottom sort
      -- i.e. @piSort a b == s0@ implies @b == s0@.
      piSortEqualsBottom s0 a b = do
        underAbstraction_ b $ equalSort s0
        -- we may have instantiated some metas, so @a@ could reduce
        a <- reduce a
        case funSort' a s0 of
          Just s  -> equalSort s s0
          Nothing -> addConstraint $ SortCmp CmpEq (funSort a s0) s0
      impossibleSort s = do
        reportSLn "impossible" 10 $ unlines
          [ "equalSort: found dummy sort with description:"
          , s
          ]
        __IMPOSSIBLE__


-- -- This should probably represent face maps with a more precise type
-- toFaceMaps :: Term -> TCM [[(Int,Term)]]
-- toFaceMaps t = do
--   view <- intervalView'
--   iz <- primIZero
--   io <- primIOne
--   ineg <- (\ q t -> Def q [Apply $ Arg defaultArgInfo t]) <$> fromMaybe __IMPOSSIBLE__ <$> getPrimitiveName' "primINeg"

--   let f IZero = mzero
--       f IOne  = return []
--       f (IMin x y) = do xs <- (f . view . unArg) x; ys <- (f . view . unArg) y; return (xs ++ ys)
--       f (IMax x y) = msum $ map (f . view . unArg) [x,y]
--       f (INeg x)   = map (id -*- not) <$> (f . view . unArg) x
--       f (OTerm (Var i [])) = return [(i,True)]
--       f (OTerm _) = return [] -- what about metas? we should suspend? maybe no metas is a precondition?
--       isConsistent xs = all (\ xs -> length xs == 1) . map nub . Map.elems $ xs  -- optimize by not doing generate + filter
--       as = map (map (id -*- head) . Map.toAscList) . filter isConsistent . map (Map.fromListWith (++) . map (id -*- (:[]))) $ (f (view t))
--   xs <- mapM (mapM (\ (i,b) -> (,) i <$> intervalUnview (if b then IOne else IZero))) as
--   return xs

forallFaceMaps :: Term -> (Map.Map Int Bool -> MetaId -> Term -> TCM a) -> (Substitution -> TCM a) -> TCM [a]
forallFaceMaps t kb k = do
  as <- decomposeInterval t
  boolToI <- do
    io <- primIOne
    iz <- primIZero
    return (\b -> if b then io else iz)
  forM as $ \ (ms,ts) -> do
   ifBlockeds ts (kb ms) $ \ _ _ -> do
    let xs = map (id -*- boolToI) $ Map.toAscList ms
    cxt <- asksTC envContext
    (cxt',sigma) <- substContextN cxt xs
    resolved <- forM xs (\ (i,t) -> (,) <$> lookupBV i <*> return (applySubst sigma t))
    updateContext sigma (const cxt') $
      addBindings resolved $ do
        cl <- buildClosure ()
        tel <- getContextTelescope
        m <- currentModule
        sub <- getModuleParameterSub m
        reportSLn "conv.forall" 10 $ unlines [replicate 10 '-'
                                             , show (envCurrentModule $ clEnv cl)
                                             , show (envLetBindings $ clEnv cl)
                                             , show tel -- (toTelescope $ envContext $ clEnv cl)
                                             , show sigma
                                             , show m
                                             , show sub]

        k sigma
  where
    -- TODO Andrea: inefficient because we try to reduce the ts which we know are in whnf
    ifBlockeds ts blocked unblocked = do
      and <- getPrimitiveTerm "primIMin"
      io  <- primIOne
      let t = foldr (\ x r -> and `apply` [argN x,argN r]) io ts
      ifBlocked t blocked unblocked
    addBindings [] m = m
    addBindings ((Dom{domInfo = info,unDom = (nm,ty)},t):bs) m = addLetBinding info nm t ty (addBindings bs m)

    substContextN :: Context -> [(Int,Term)] -> TCM (Context , Substitution)
    substContextN c [] = return (c, idS)
    substContextN c ((i,t):xs) = do
      (c', sigma) <- substContext i t c
      (c'', sigma')  <- substContextN c' (map (subtract 1 -*- applySubst sigma) xs)
      return (c'', applySubst sigma' sigma)


    -- assumes the term can be typed in the shorter telescope
    -- the terms we get from toFaceMaps are closed.
    substContext :: Int -> Term -> Context -> TCM (Context , Substitution)
    substContext i t [] = __IMPOSSIBLE__
    substContext i t (x:xs) | i == 0 = return $ (xs , singletonS 0 t)
    substContext i t (x:xs) | i > 0 = do
                                  (c,sigma) <- substContext (i-1) t xs
                                  let e = applySubst sigma x
                                  return (e:c, liftS 1 sigma)
    substContext i t (x:xs) = __IMPOSSIBLE__

compareInterval :: Comparison -> Type -> Term -> Term -> TCM ()
compareInterval cmp i t u = do
  reportSDoc "tc.conv.interval" 15 $
    sep [ "{ compareInterval" <+> prettyTCM t <+> "=" <+> prettyTCM u ]
  tb <- reduceB t
  ub <- reduceB u
  let t = ignoreBlocking tb
      u = ignoreBlocking ub
  it <- decomposeInterval' t
  iu <- decomposeInterval' u
  case () of
    _ | blockedOrMeta tb || blockedOrMeta ub -> do
      -- in case of metas we wouldn't be able to make progress by how we deal with de morgan laws.
      -- (because the constraints generated by decomposition are sufficient but not necessary).
      -- but we could still prune/solve some metas by comparing the terms as atoms.
      -- also if blocked we won't find the terms conclusively unequal(?) so compareAtom
      -- won't report type errors when we should accept.
      interval <- elInf $ primInterval
      compareAtom CmpEq interval t u
    _ | otherwise -> do
      x <- leqInterval it iu
      y <- leqInterval iu it
      let final = isCanonical it && isCanonical iu
      if x && y then reportSDoc "tc.conv.interval" 15 $ "Ok! }" else
        if final then typeError $ UnequalTerms cmp t u i
                 else do
                   reportSDoc "tc.conv.interval" 15 $ "Giving up! }"
                   patternViolation
 where
   blockedOrMeta Blocked{} = True
   blockedOrMeta (NotBlocked _ (MetaV{})) = True
   blockedOrMeta _ = False


type Conj = (Map.Map Int (Set.Set Bool),[Term])

isCanonical :: [Conj] -> Bool
isCanonical = all (null . snd)

-- | leqInterval r q = r ≤ q in the I lattice.
-- (∨ r_i) ≤ (∨ q_j)  iff  ∀ i. ∃ j. r_i ≤ q_j
leqInterval :: [Conj] -> [Conj] -> TCM Bool
leqInterval r q =
  and <$> forM r (\ r_i ->
   or <$> forM q (\ q_j -> leqConj r_i q_j))  -- TODO shortcut

-- | leqConj r q = r ≤ q in the I lattice, when r and q are conjuctions.
-- ' (∧ r_i)   ≤ (∧ q_j)               iff
-- ' (∧ r_i)   ∧ (∧ q_j)   = (∧ r_i)   iff
-- ' {r_i | i} ∪ {q_j | j} = {r_i | i} iff
-- ' {q_j | j} ⊆ {r_i | i}
leqConj :: Conj -> Conj -> TCM Bool
leqConj (rs,rst) (qs,qst) = do
  case toSet qs `Set.isSubsetOf` toSet rs of
    False -> return False
    True  -> do
      interval <- elInf $ primInterval

      -- we don't want to generate new constraints here because
      -- 1) in some situations the same constraint would get generated twice.
      -- 2) unless things are completely accepted we are going to
      --    throw patternViolation in compareInterval.
      let eqT t u = tryConversion (compareAtom CmpEq interval t u)

      let listSubset ts us = and <$> forM ts (\ t ->
                              or <$> forM us (\ u -> eqT t u)) -- TODO shortcut
      listSubset qst rst
  where
    toSet m = Set.fromList [ (i,b) | (i,bs) <- Map.toList m, b <- Set.toList bs]


-- | equalTermOnFace φ A u v = _ , φ ⊢ u = v : A
equalTermOnFace :: Term -> Type -> Term -> Term -> TCM ()
equalTermOnFace = compareTermOnFace CmpEq

compareTermOnFace :: Comparison -> Term -> Type -> Term -> Term -> TCM ()
compareTermOnFace = compareTermOnFace' compareTerm

compareTermOnFace' :: (Comparison -> Type -> Term -> Term -> TCM ()) -> Comparison -> Term -> Type -> Term -> Term -> TCM ()
compareTermOnFace' k cmp phi ty u v = do
  phi <- reduce phi
  _ <- forallFaceMaps phi postponed
         $ \ alpha -> k cmp (applySubst alpha ty) (applySubst alpha u) (applySubst alpha v)
  return ()
 where
  postponed ms i psi = do
    phi <- runNamesT [] $ do
             imin <- cl $ getPrimitiveTerm "primIMin"
             ineg <- cl $ getPrimitiveTerm "primINeg"
             psi <- open psi
             let phi = foldr (\ (i,b) r -> do i <- open (var i); pure imin <@> (if b then i else pure ineg <@> i) <@> r)
                          psi (Map.toList ms) -- TODO Andrea: make a view?
             phi
    addConstraint (ValueCmpOnFace cmp phi ty u v)

---------------------------------------------------------------------------
-- * Definitions
---------------------------------------------------------------------------

bothAbsurd :: QName -> QName -> TCM Bool
bothAbsurd f f'
  | isAbsurdLambdaName f, isAbsurdLambdaName f' = do
      -- Double check we are really dealing with absurd lambdas:
      -- Their functions should not have bodies.
      def  <- getConstInfo f
      def' <- getConstInfo f'
      case (theDef def, theDef def') of
        (Function{ funClauses = [Clause{ clauseBody = Nothing }] },
         Function{ funClauses = [Clause{ clauseBody = Nothing }] }) -> return True
        _ -> return False
  | otherwise = return False
