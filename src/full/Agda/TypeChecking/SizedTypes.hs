{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.SizedTypes where

import Prelude hiding (null)

import Control.Monad.Writer

import qualified Data.Foldable as Fold
import qualified Data.List as List
import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.Constraints

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.List as List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.NonemptyList
import Agda.Utils.Null
import Agda.Utils.Pretty (Pretty)
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Tuple

import qualified Agda.Utils.Pretty as P
import qualified Agda.Utils.Warshall as W

import Agda.Utils.Impossible

------------------------------------------------------------------------
-- * SIZELT stuff
------------------------------------------------------------------------

-- | Check whether a type is either not a SIZELT or a SIZELT that is non-empty.
checkSizeLtSat :: Term -> TCM ()
checkSizeLtSat t = whenM haveSizeLt $ do
  reportSDoc "tc.size" 10 $ do
    tel <- getContextTelescope
    sep
      [ "checking that " <+> prettyTCM t <+> " is not an empty type of sizes"
      , if null tel then empty else do
        "in context " <+> inTopContext (prettyTCM tel)
      ]
  reportSLn "tc.size" 60 $ "- raw type = " ++ show t
  let postpone :: Term -> TCM ()
      postpone t = do
        reportSDoc "tc.size.lt" 20 $ sep
          [ "- postponing `not empty type of sizes' check for " <+> prettyTCM t ]
        addConstraint $ CheckSizeLtSat t
  let ok :: TCM ()
      ok = reportSLn "tc.size.lt" 20 $ "- succeeded: not an empty type of sizes"
  ifBlocked t (const postpone) $ \ _ t -> do
    reportSLn "tc.size.lt" 20 $ "- type is not blocked"
    caseMaybeM (isSizeType t) ok $ \ b -> do
      reportSLn "tc.size.lt" 20 $ " - type is a size type"
      case b of
        BoundedNo -> ok
        BoundedLt b -> do
          reportSDoc "tc.size.lt" 20 $ " - type is SIZELT" <+> prettyTCM b
          ifBlocked b (\ _ _ -> postpone t) $ \ _ b -> do
            reportSLn "tc.size.lt" 20 $ " - size bound is not blocked"
            catchConstraint (CheckSizeLtSat t) $ do
              unlessM (checkSizeNeverZero b) $ do
                typeError . GenericDocError =<< do
                  "Possibly empty type of sizes " <+> prettyTCM t

-- | Precondition: Term is reduced and not blocked.
--   Throws a 'patternViolation' if undecided
checkSizeNeverZero :: Term -> TCM Bool
checkSizeNeverZero u = do
  v <- sizeView u
  case v of
    SizeInf     -> return True  -- OK, infty is never 0.
    SizeSuc{}   -> return True  -- OK, a + 1 is never 0.
    OtherSize u ->
      case u of
        Var i [] -> checkSizeVarNeverZero i
        -- neutral sizes cannot be guaranteed > 0
        _ -> return False

-- -- | A size variable is never zero if it is the strict upper bound of
-- --   some other size variable in context.
-- --   Eg. @i : Size, j : Size< i@ |- i is never zero.
-- --   Throws a 'patternViolation' if undecided.
-- checkSizeVarNeverZero :: Int -> TCM Bool
-- checkSizeVarNeverZero i = do
--   -- Looking for a variable j : Size< i, we can restrict to the last i
--   -- entries, as this variable necessarily has been defined later than i.
--   doms <- take i <$> getContext
--   -- We raise each type to make sense in the current context.
--   let ts = zipWith raise [1..] $ map (snd . unDom) doms
--   reportSDoc "tc.size" 15 $ sep
--     [ "checking that size " <+> prettyTCM (var i) <+> " is never 0"
--     , "in context " <+> do sep $ map prettyTCM ts
--     ]
--   foldr f (return False) ts
--   where
--   f t cont = do
--     -- If we encounter a blocked type in the context, we cannot
--     -- definitely say no.
--     let yes     = return True
--         no      = cont
--         perhaps = cont >>= \ res -> if res then return res else patternViolation
--     ifBlocked t (\ _ _ -> perhaps) $ \ t -> do
--       caseMaybeM (isSizeType t) no $ \ b -> do
--         case b of
--           BoundedNo -> no
--           BoundedLt u -> ifBlocked u (\ _ _ -> perhaps) $ \ u -> do
--             case u of
--                Var i' [] | i == i' -> yes
--                _ -> no


-- | Checks that a size variable is ensured to be @> 0@.
--   E.g. variable @i@ cannot be zero in context
--   @(i : Size) (j : Size< ↑ ↑ i) (k : Size< j) (k' : Size< k)@.
--   Throws a 'patternViolation' if undecided.
checkSizeVarNeverZero :: Int -> TCM Bool
checkSizeVarNeverZero i = do
  reportSDoc "tc.size" 20 $ "checkSizeVarNeverZero" <+> prettyTCM (var i)
  -- Looking for the minimal value for size variable i,
  -- we can restrict to the last i
  -- entries, as only these can contain i in an upper bound.
  ts <- map (snd . unDom) . take i <$> getContext
  -- If we encountered a blocking meta in the context, we cannot
  -- say ``no'' for sure.
  (n, Any meta) <- runWriterT $ minSizeValAux ts $ repeat 0
  if n > 0 then return True else
    if meta then patternViolation else return False
  where
  -- Compute the least valuation for size context ts above the
  -- given valuation and return its last value.
  minSizeValAux :: [Type] -> [Int] -> WriterT Any TCM Int
  minSizeValAux _        []      = __IMPOSSIBLE__
  minSizeValAux []       (n : _) = return n
  minSizeValAux (t : ts) (n : ns) = do
    reportSDoc "tc.size" 60 $
       text ("minSizeVal (n:ns) = " ++ show (take (length ts + 2) $ n:ns) ++
             " t =") <+> (text . show) t  -- prettyTCM t  -- Wrong context!
    -- n is the min. value for variable 0 which has type t.
    let cont = minSizeValAux ts ns
        perhaps = tell (Any True) >> cont
    -- If we encounter a blocked type in the context, we cannot
    -- give a definite answer.
    ifBlocked t (\ _ _ -> perhaps) $ \ _ t -> do
      caseMaybeM (liftTCM $ isSizeType t) cont $ \ b -> do
        case b of
          BoundedNo -> cont
          BoundedLt u -> ifBlocked u (\ _ _ -> perhaps) $ \ _ u -> do
            reportSLn "tc.size" 60 $ "minSizeVal upper bound u = " ++ show u
            v <- liftTCM $ deepSizeView u
            case v of
              -- Variable 0 has bound @(< j + m)@
              -- meaning that @minval(j) > n - m@, i.e., @minval(j) >= n+1-m@.
              -- Thus, we update the min value for @j@ with function @(max (n+1-m))@.
              DSizeVar j m -> do
                reportSLn "tc.size" 60 $ "minSizeVal upper bound v = " ++ show v
                let ns' = List.updateAt j (max $ n+1-m) ns
                reportSLn "tc.size" 60 $ "minSizeVal ns' = " ++ show (take (length ts + 1) ns')
                minSizeValAux ts ns'
              DSizeMeta{} -> perhaps
              _ -> cont

-- | Check whether a variable in the context is bounded by a size expression.
--   If @x : Size< a@, then @a@ is returned.
isBounded :: (MonadReduce m, MonadTCEnv m, HasBuiltins m)
          => Nat -> m BoundedSize
isBounded i = do
  t <- reduce =<< typeOfBV i
  case unEl t of
    Def x [Apply u] -> do
      sizelt <- getBuiltin' builtinSizeLt
      return $ if (Just (Def x []) == sizelt) then BoundedLt $ unArg u else BoundedNo
    _ -> return BoundedNo

-- | Whenever we create a bounded size meta, add a constraint
--   expressing the bound.
--   In @boundedSizeMetaHook v tel a@, @tel@ includes the current context.
boundedSizeMetaHook
  :: ( MonadConstraint m
     , MonadTCEnv m
     , ReadTCState m
     , MonadAddContext m
     , HasOptions m
     , HasBuiltins m
     )
  => Term -> Telescope -> Type -> m ()
boundedSizeMetaHook v tel0 a = do
  res <- isSizeType a
  case res of
    Just (BoundedLt u) -> do
      n <- getContextSize
      let tel | n > 0     = telFromList $ drop n $ telToList tel0
              | otherwise = tel0
      addContext tel $ do
        v <- sizeSuc 1 $ raise (size tel) v `apply` teleArgs tel
        -- compareSizes CmpLeq v u
        size <- sizeType
        addConstraint $ ValueCmp CmpLeq (AsTermsOf size) v u
    _ -> return ()

-- | @trySizeUniv cmp t m n x els1 y els2@
--   is called as a last resort when conversion checking @m `cmp` n : t@
--   failed for definitions @m = x els1@ and @n = y els2@,
--   where the heads @x@ and @y@ are not equal.
--
--   @trySizeUniv@ accounts for subtyping between SIZELT and SIZE,
--   like @Size< i =< Size@.
--
--   If it does not succeed it reports failure of conversion check.
trySizeUniv
  :: MonadConversion m
  => Comparison -> CompareAs -> Term -> Term
  -> QName -> Elims -> QName -> Elims -> m ()
trySizeUniv cmp t m n x els1 y els2 = do
  let failure = typeError $ UnequalTerms cmp m n t
      forceInfty u = compareSizes CmpEq (unArg u) =<< primSizeInf
  -- Get the SIZE built-ins.
  (size, sizelt) <- flip catchError (const failure) $ do
     Def size   _ <- primSize
     Def sizelt _ <- primSizeLt
     return (size, sizelt)
  case (cmp, els1, els2) of
     -- Case @Size< _ <= Size@: true.
     (CmpLeq, [_], [])  | x == sizelt && y == size -> return ()
     -- Case @Size< u = Size@: forces @u = ∞@.
     (_, [Apply u], []) | x == sizelt && y == size -> forceInfty u
     (_, [], [Apply u]) | x == size && y == sizelt -> forceInfty u
     -- This covers all cases for SIZE and SIZELT.
     -- The remaining case is for @x@ and @y@ which are not size built-ins.
     _                                             -> failure

------------------------------------------------------------------------
-- * Size views that 'reduce'.
------------------------------------------------------------------------

-- | Compute the deep size view of a term.
--   Precondition: sized types are enabled.
deepSizeView :: Term -> TCM DeepSizeView
deepSizeView v = do
  Def inf [] <- primSizeInf
  Def suc [] <- primSizeSuc
  let loop v = do
        v <- reduce v
        case v of
          Def x []        | x == inf -> return $ DSizeInf
          Def x [Apply u] | x == suc -> sizeViewSuc_ suc <$> loop (unArg u)
          Var i []                   -> return $ DSizeVar i 0
          MetaV x us                 -> return $ DSizeMeta x us 0
          _                          -> return $ DOtherSize v
  loop v

sizeMaxView :: (MonadReduce m, HasBuiltins m) => Term -> m SizeMaxView
sizeMaxView v = do
  inf <- getBuiltinDefName builtinSizeInf
  suc <- getBuiltinDefName builtinSizeSuc
  max <- getBuiltinDefName builtinSizeMax
  let loop v = do
        v <- reduce v
        case v of
          Def x []                   | Just x == inf -> return $ singleton $ DSizeInf
          Def x [Apply u]            | Just x == suc -> maxViewSuc_ (fromJust suc) <$> loop (unArg u)
          Def x [Apply u1, Apply u2] | Just x == max -> maxViewMax <$> loop (unArg u1) <*> loop (unArg u2)
          Var i []                      -> return $ singleton $ DSizeVar i 0
          MetaV x us                    -> return $ singleton $ DSizeMeta x us 0
          _                             -> return $ singleton $ DOtherSize v
  loop v

------------------------------------------------------------------------
-- * Size comparison that might add constraints.
------------------------------------------------------------------------

-- | Compare two sizes.
compareSizes :: (MonadConversion m) => Comparison -> Term -> Term -> m ()
compareSizes cmp u v = verboseBracket "tc.conv.size" 10 "compareSizes" $ do
  reportSDoc "tc.conv.size" 10 $ vcat
    [ "Comparing sizes"
    , nest 2 $ sep [ prettyTCM u <+> prettyTCM cmp
                   , prettyTCM v
                   ]
    ]
  verboseS "tc.conv.size" 60 $ do
    u <- reduce u
    v <- reduce v
    reportSDoc "tc.conv.size" 60 $
      nest 2 $ sep [ pretty u <+> prettyTCM cmp
                   , pretty v
                   ]
  us <- sizeMaxView u
  vs <- sizeMaxView v
  compareMaxViews cmp us vs

-- | Compare two sizes in max view.
compareMaxViews :: (MonadConversion m) => Comparison -> SizeMaxView -> SizeMaxView -> m ()
compareMaxViews cmp us vs = case (cmp, us, vs) of
  (CmpLeq, _, (DSizeInf :! _)) -> return ()
  (cmp, u:![], v:![]) -> compareSizeViews cmp u v
  (CmpLeq, us, v:![]) -> Fold.forM_ us $ \ u -> compareSizeViews cmp u v
  (CmpLeq, us, vs)    -> Fold.forM_ us $ \ u -> compareBelowMax u vs
  (CmpEq,  us, vs)    -> do
    compareMaxViews CmpLeq us vs
    compareMaxViews CmpLeq vs us

-- | @compareBelowMax u vs@ checks @u <= max vs@.  Precondition: @size vs >= 2@
compareBelowMax :: (MonadConversion m) => DeepSizeView -> SizeMaxView -> m ()
compareBelowMax u vs = verboseBracket "tc.conv.size" 45 "compareBelowMax" $ do
  reportSDoc "tc.conv.size" 45 $ sep
    [ pretty u
    , pretty CmpLeq
    , pretty vs
    ]
  -- When trying several alternatives, we do not assign metas
  -- and also do not produce constraints (see 'giveUp' below).
  -- Andreas, 2019-03-28, issue #3600.
  alt (dontAssignMetas $ Fold.foldr1 alt $ fmap (compareSizeViews CmpLeq u) vs) $ do
    reportSDoc "tc.conv.size" 45 $ vcat
      [ "compareBelowMax: giving up"
      ]
    u <- unDeepSizeView u
    v <- unMaxView vs
    size <- sizeType
    giveUp CmpLeq size u v
  where
  alt c1 c2 = c1 `catchError` const c2

compareSizeViews :: (MonadConversion m) => Comparison -> DeepSizeView -> DeepSizeView -> m ()
compareSizeViews cmp s1' s2' = do
  reportSDoc "tc.conv.size" 45 $ hsep
    [ "compareSizeViews"
    , pretty s1'
    , pretty cmp
    , pretty s2'
    ]
  size <- sizeType
  let (s1, s2) = removeSucs (s1', s2')
      withUnView cont = do
        u <- unDeepSizeView s1
        v <- unDeepSizeView s2
        cont u v
      failure = withUnView $ \ u v -> typeError $ UnequalTerms cmp u v (AsTermsOf size)
      continue cmp = withUnView $ compareAtom cmp (AsTermsOf size)
  case (cmp, s1, s2) of
    (CmpLeq, _,            DSizeInf)   -> return ()
    (CmpEq,  DSizeInf,     DSizeInf)   -> return ()
    (CmpEq,  DSizeVar{},   DSizeInf)   -> failure
    (_    ,  DSizeInf,     DSizeVar{}) -> failure
    (_    ,  DSizeInf,     _         ) -> continue CmpEq
    (CmpLeq, DSizeVar i n, DSizeVar j m) | i == j -> unless (n <= m) failure
    (CmpLeq, DSizeVar i n, DSizeVar j m) | i /= j -> do
       res <- isBounded i
       case res of
         BoundedNo -> failure
         BoundedLt u' -> do
            -- now we have i < u', in the worst case i+1 = u'
            -- and we want to check i+n <= v
            v <- unDeepSizeView s2
            if n > 0 then do
              u'' <- sizeSuc (n - 1) u'
              compareSizes cmp u'' v
             else compareSizes cmp u' =<< sizeSuc 1 v
    (CmpLeq, s1,        s2)         -> withUnView $ \ u v -> do
      unlessM (trivial u v) $ giveUp CmpLeq size u v
    (CmpEq, s1, s2) -> continue cmp

-- | If 'envAssignMetas' then postpone as constraint, otherwise, fail hard.
--   Failing is required if we speculatively test several alternatives.
giveUp :: (MonadConversion m) => Comparison -> Type -> Term -> Term -> m ()
giveUp cmp size u v =
  ifM (asksTC envAssignMetas)
    {-then-} (addConstraint $ ValueCmp CmpLeq (AsTermsOf size) u v)
    {-else-} (typeError $ UnequalTerms cmp u v (AsTermsOf size))

-- | Checked whether a size constraint is trivial (like @X <= X+1@).
trivial :: (MonadConversion m) => Term -> Term -> m Bool
trivial u v = do
    a@(e , n ) <- oldSizeExpr u
    b@(e', n') <- oldSizeExpr v
    let triv = e == e' && n <= n'
          -- Andreas, 2012-02-24  filtering out more trivial constraints fixes
          -- test/lib-succeed/SizeInconsistentMeta4.agda
    reportSDoc "tc.conv.size" 60 $
      nest 2 $ sep [ if triv then "trivial constraint" else empty
                   , pretty a <+> "<="
                   , pretty b
                   ]
    return triv
  `catchError` \_ -> return False

------------------------------------------------------------------------
-- * Size constraints.
------------------------------------------------------------------------

-- | Test whether a problem consists only of size constraints.
isSizeProblem :: (ReadTCState m, HasOptions m, HasBuiltins m) => ProblemId -> m Bool
isSizeProblem pid = andM . map (isSizeConstraint . theConstraint) =<< getConstraintsForProblem pid

-- | Test is a constraint speaks about sizes.
isSizeConstraint :: (HasOptions m, HasBuiltins m) => Closure Constraint -> m Bool
isSizeConstraint Closure{ clValue = ValueCmp _ (AsTermsOf s) _ _ } = isJust <$> isSizeType s
isSizeConstraint _ = return False

-- | Take out all size constraints (DANGER!).
takeSizeConstraints :: TCM [Closure Constraint]
takeSizeConstraints = do
  test <- isSizeTypeTest
  let sizeConstraint :: Closure Constraint -> Bool
      sizeConstraint cl@Closure{ clValue = ValueCmp CmpLeq (AsTermsOf s) _ _ }
              | isJust (test $ unEl s) = True
      sizeConstraint _ = False
  cs <- filter sizeConstraint . map theConstraint <$> getAllConstraints
  dropConstraints $ sizeConstraint . theConstraint
  return cs

-- | Find the size constraints.
getSizeConstraints :: TCM [Closure Constraint]
getSizeConstraints = do
  test <- isSizeTypeTest
  let sizeConstraint :: Closure Constraint -> Bool
      sizeConstraint cl@Closure{ clValue = ValueCmp CmpLeq (AsTermsOf s) _ _ }
              | isJust (test $ unEl s) = True
      sizeConstraint _ = False
  filter sizeConstraint . map theConstraint <$> getAllConstraints

-- | Return a list of size metas and their context.
getSizeMetas :: Bool -> TCM [(MetaId, Type, Telescope)]
getSizeMetas interactionMetas = do
  test <- isSizeTypeTest
  catMaybes <$> do
    getOpenMetas >>= do
      mapM $ \ m -> do
        let no = return Nothing
        mi <- lookupMeta m
        case mvJudgement mi of
          _ | BlockedConst{} <- mvInstantiation mi -> no  -- Blocked terms should not be touched (#2637, #2881)
          HasType _ cmp a -> do
            TelV tel b <- telView a
            -- b is reduced
            caseMaybe (test $ unEl b) no $ \ _ -> do
              let yes = return $ Just (m, a, tel)
              if interactionMetas then yes else do
                ifM (isJust <$> isInteractionMeta m) no yes
          _ -> no

{- ROLLED BACK
getSizeMetas :: TCM ([(MetaId, Int)], [SizeConstraint])
getSizeMetas = do
  ms <- getOpenMetas
  test <- isSizeTypeTest
  let sizeCon m = do
        let nothing  = return ([], [])
        mi <- lookupMeta m
        case mvJudgement mi of
          HasType _ a -> do
            TelV tel b <- telView =<< instantiateFull a
            let noConstr = return ([(m, size tel)], [])
            case test b of
              Nothing            -> nothing
              Just BoundedNo     -> noConstr
              Just (BoundedLt u) -> noConstr
{- WORKS NOT
              Just (BoundedLt u) -> flip catchError (const $ noConstr) $ do
                -- we assume the metavariable is used in an
                -- extension of its creation context
                ctxIds <- getContextId
                let a = SizeMeta m $ take (size tel) $ reverse ctxIds
                (b, n) <- oldSizeExpr u
                return ([(m, size tel)], [Leq a (n-1) b])
-}
          _ -> nothing
  (mss, css) <- unzip <$> mapM sizeCon ms
  return (concat mss, concat css)
-}

------------------------------------------------------------------------
-- * Size constraint solving.
------------------------------------------------------------------------

-- | Atomic size expressions.
data OldSizeExpr
  = SizeMeta MetaId [Int] -- ^ A size meta applied to de Bruijn indices.
  | Rigid Int             -- ^ A de Bruijn index.
  deriving (Eq, Show)

instance Pretty OldSizeExpr where
  pretty (SizeMeta m _) = P.text $ "X" ++ show (fromIntegral m :: Int)
  pretty (Rigid i)      = P.text $ "c" ++ show i

-- | Size constraints we can solve.
data OldSizeConstraint
  = Leq OldSizeExpr Int OldSizeExpr
    -- ^ @Leq a +n b@ represents @a =< b + n@.
    --   @Leq a -n b@ represents @a + n =< b@.
  deriving (Show)

instance Pretty OldSizeConstraint where
  pretty (Leq a n b)
    | n == 0    = P.pretty a P.<+> "=<" P.<+> P.pretty b
    | n > 0     = P.pretty a P.<+> "=<" P.<+> P.pretty b P.<+> "+" P.<+> P.text (show n)
    | otherwise = P.pretty a P.<+> "+" P.<+> P.text (show (-n)) P.<+> "=<" P.<+> P.pretty b

-- | Compute a set of size constraints that all live in the same context
--   from constraints over terms of type size that may live in different
--   contexts.
--
--   cf. 'Agda.TypeChecking.LevelConstraints.simplifyLevelConstraint'
oldComputeSizeConstraints :: [Closure Constraint] -> TCM [OldSizeConstraint]
oldComputeSizeConstraints [] = return [] -- special case to avoid maximum []
oldComputeSizeConstraints cs = catMaybes <$> mapM oldComputeSizeConstraint leqs
  where
    -- get the constraints plus contexts they are defined in
    gammas       = map (envContext . clEnv) cs
    ls           = map clValue cs
    -- compute the longest context (common water level)
    ns           = map size gammas
    waterLevel   = maximum ns
    -- lift all constraints to live in the longest context
    -- (assuming this context is an extension of the shorter ones)
    -- by raising the de Bruijn indices
    leqs = zipWith raise (map (waterLevel -) ns) ls

-- | Turn a constraint over de Bruijn indices into a size constraint.
oldComputeSizeConstraint :: Constraint -> TCM (Maybe OldSizeConstraint)
oldComputeSizeConstraint c =
  case c of
    ValueCmp CmpLeq _ u v -> do
        reportSDoc "tc.size.solve" 50 $ sep
          [ "converting size constraint"
          , prettyTCM c
          ]
        (a, n) <- oldSizeExpr u
        (b, m) <- oldSizeExpr v
        return $ Just $ Leq a (m - n) b
      `catchError` \ err -> case err of
        PatternErr{} -> return Nothing
        _            -> throwError err
    _ -> __IMPOSSIBLE__

-- | Turn a term with de Bruijn indices into a size expression with offset.
--
--   Throws a 'patternViolation' if the term isn't a proper size expression.
oldSizeExpr :: (MonadReduce m, MonadDebug m, MonadError TCErr m, HasBuiltins m)
            => Term -> m (OldSizeExpr, Int)
oldSizeExpr u = do
  u <- reduce u -- Andreas, 2009-02-09.
                -- This is necessary to surface the solutions of metavariables.
  reportSDoc "tc.conv.size" 60 $ "oldSizeExpr:" <+> prettyTCM u
  s <- sizeView u
  case s of
    SizeInf     -> patternViolation
    SizeSuc u   -> mapSnd (+1) <$> oldSizeExpr u
    OtherSize u -> case u of
      Var i []  -> return (Rigid i, 0)
      MetaV m es | Just xs <- mapM isVar es, fastDistinct xs
                -> return (SizeMeta m xs, 0)
      _ -> patternViolation
  where
    isVar (Proj{})  = Nothing
    isVar (IApply _ _ v) = isVar (Apply (defaultArg v))
    isVar (Apply v) = case unArg v of
      Var i [] -> Just i
      _        -> Nothing

-- | Compute list of size metavariables with their arguments
--   appearing in a constraint.
flexibleVariables :: OldSizeConstraint -> [(MetaId, [Int])]
flexibleVariables (Leq a _ b) = flex a ++ flex b
  where
    flex (Rigid _)       = []
    flex (SizeMeta m xs) = [(m, xs)]

-- | Convert size constraint into form where each meta is applied
--   to indices @0,1,..,n-1@ where @n@ is the arity of that meta.
--
--   @X[σ] <= t@ becomes @X[id] <= t[σ^-1]@
--
--   @X[σ] ≤ Y[τ]@ becomes @X[id] ≤ Y[τ[σ^-1]]@ or @X[σ[τ^1]] ≤ Y[id]@
--   whichever is defined.  If none is defined, we give up.
--
oldCanonicalizeSizeConstraint :: OldSizeConstraint -> Maybe OldSizeConstraint
oldCanonicalizeSizeConstraint c@(Leq a n b) =
  case (a,b) of
    (Rigid{}, Rigid{})       -> return c
    (SizeMeta m xs, Rigid i) -> do
      j <- List.findIndex (==i) xs
      return $ Leq (SizeMeta m [0..size xs-1]) n (Rigid j)
    (Rigid i, SizeMeta m xs) -> do
      j <- List.findIndex (==i) xs
      return $ Leq (Rigid j) n (SizeMeta m [0..size xs-1])
    (SizeMeta m xs, SizeMeta l ys)
         -- try to invert xs on ys
       | Just ys' <- mapM (\ y -> List.findIndex (==y) xs) ys ->
           return $ Leq (SizeMeta m [0..size xs-1]) n (SizeMeta l ys')
         -- try to invert ys on xs
       | Just xs' <- mapM (\ x -> List.findIndex (==x) ys) xs ->
           return $ Leq (SizeMeta m xs') n (SizeMeta l [0..size ys-1])
         -- give up
       | otherwise -> Nothing

-- | Main function.
--   Uses the old solver for size constraints using "Agda.Utils.Warshall".
--   This solver does not smartly use size hypotheses @j : Size< i@.
--   It only checks that its computed solution is compatible
oldSolveSizeConstraints :: TCM ()
oldSolveSizeConstraints = whenM haveSizedTypes $ do
  reportSLn "tc.size.solve" 70 $ "Considering to solve size constraints"
  cs0 <- getSizeConstraints
  cs <- oldComputeSizeConstraints cs0
  ms <- getSizeMetas True -- get all size metas, also interaction metas

  when (not (null cs) || not (null ms)) $ do
    reportSLn "tc.size.solve" 10 $ "Solving size constraints " ++ show cs

    cs <- return $ mapMaybe oldCanonicalizeSizeConstraint cs
    reportSLn "tc.size.solve" 10 $ "Canonicalized constraints: " ++ show cs

    let -- Error for giving up
        cannotSolve = typeError . GenericDocError =<<
          vcat ("Cannot solve size constraints" : map prettyTCM cs0)

        -- Size metas in constraints.
        metas0 :: [(MetaId, Int)]  -- meta id + arity
        metas0 = List.nub $ map (mapSnd length) $ concatMap flexibleVariables cs

        -- Unconstrained size metas that do not occur in constraints.
        metas1 :: [(MetaId, Int)]
        metas1 = forMaybe ms $ \ (m, _, tel) ->
          maybe (Just (m, size tel)) (const Nothing) $
            lookup m metas0

        -- All size metas
        metas = metas0 ++ metas1

    reportSLn "tc.size.solve" 15 $ "Metas: " ++ show metas0 ++ ", " ++ show metas1

    verboseS "tc.size.solve" 20 $
        -- debug print the type of all size metas
        forM_ metas $ \ (m, _) ->
            reportSDoc "tc.size.solve" 20 $ prettyTCM =<< mvJudgement <$> lookupMeta m

    -- Run the solver.
    unlessM (oldSolver metas cs) cannotSolve

    -- Double-checking the solution.

    -- Andreas, 2012-09-19
    -- The returned solution might not be consistent with
    -- the hypotheses on rigid vars (j : Size< i).
    -- Thus, we double check that all size constraints
    -- have been solved correctly.
    flip catchError (const cannotSolve) $
      noConstraints $
        forM_ cs0 $ \ cl -> enterClosure cl solveConstraint


-- | Old solver for size constraints using "Agda.Utils.Warshall".
--   This solver does not smartly use size hypotheses @j : Size< i@.
oldSolver
  :: [(MetaId, Int)]      -- ^ Size metas and their arity.
  -> [OldSizeConstraint]  -- ^ Size constraints (in preprocessed form).
  -> TCM Bool             -- ^ Returns @False@ if solver fails.
oldSolver metas cs = do
  let cannotSolve    = return False
      mkFlex (m, ar) = W.NewFlex (fromIntegral m) $ \ i -> fromIntegral i < ar
      mkConstr (Leq a n b)  = W.Arc (mkNode a) n (mkNode b)
      mkNode (Rigid i)      = W.Rigid $ W.RVar i
      mkNode (SizeMeta m _) = W.Flex $ fromIntegral m

  -- run the Warshall solver
  case W.solve $ map mkFlex metas ++ map mkConstr cs of
    Nothing  -> cannotSolve
    Just sol -> do
      reportSLn "tc.size.solve" 10 $ "Solved constraints: " ++ show sol
      suc   <- primSizeSuc
      infty <- primSizeInf
      let plus v 0 = v
          plus v n = suc `apply1` plus v (n - 1)

          inst (i, e) = do

            let m  = fromIntegral i  -- meta variable identifier
                ar = fromMaybe __IMPOSSIBLE__ $ lookup m metas  -- meta var arity

                term (W.SizeConst W.Infinite) = infty
                term (W.SizeVar j n) | j < ar = plus (var $ ar - j - 1) n
                term _                        = __IMPOSSIBLE__

                tel = replicate ar $ defaultArg "s"
                -- convert size expression to term
                v = term e

            reportSDoc "tc.size.solve" 20 $ sep
              [ pretty m <+> ":="
              , nest 2 $ prettyTCM v
              ]

            -- Andreas, 2012-09-25: do not assign interaction metas to \infty
            let isInf (W.SizeConst W.Infinite) = True
                isInf _                        = False
            unlessM (((isInf e &&) . isJust <$> isInteractionMeta m) `or2M` isFrozen m) $
              assignTerm m tel v

      mapM_ inst $ Map.toList sol
      return True
