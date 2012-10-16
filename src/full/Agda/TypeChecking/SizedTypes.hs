{-# LANGUAGE CPP, PatternGuards #-}
module Agda.TypeChecking.SizedTypes where

import Control.Monad.Error
import Control.Monad

import Data.Function
import Data.List
import qualified Data.Map as Map

import Agda.Interaction.Options

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

import qualified Agda.Utils.Warshall as W
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Impossible
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Pretty (render)

#include "../undefined.h"

builtinSizeHook :: String -> QName -> Term -> Type -> TCM ()
builtinSizeHook s q e' t = do
  when (s `elem` [builtinSizeLt, builtinSizeSuc]) $ do
    modifySignature $ updateDefinition q
      $ updateDefPolarity       (const [Covariant])
      . updateDefArgOccurrences (const [StrictPos])
  when (s == builtinSizeMax) $ do
    modifySignature $ updateDefinition q
      $ updateDefPolarity       (const [Covariant, Covariant])
      . updateDefArgOccurrences (const [StrictPos, StrictPos])
{-
      . updateDefType           (const tmax)
  where
    -- TODO: max : (i j : Size) -> Size< (suc (max i j))
    tmax =
-}

-- | Compute the deep size view of a term.
--   Precondition: sized types are enabled.
deepSizeView :: Term -> TCM DeepSizeView
deepSizeView v = do
  Def inf [] <- ignoreSharing <$> primSizeInf
  Def suc [] <- ignoreSharing <$> primSizeSuc
  let loop v = do
      v <- reduce v
      case ignoreSharing v of
        Def x []  | x == inf -> return $ DSizeInf
        Def x [u] | x == suc -> sizeViewSuc_ suc <$> loop (unArg u)
        Var i []             -> return $ DSizeVar i 0
        MetaV x us           -> return $ DSizeMeta x us 0
        _                    -> return $ DOtherSize v
  loop v

sizeMaxView :: Term -> TCM SizeMaxView
sizeMaxView v = do
  inf <- getBuiltinDefName builtinSizeInf
  suc <- getBuiltinDefName builtinSizeSuc
  max <- getBuiltinDefName builtinSizeMax
  let loop v = do
      v <- reduce v
      case v of
        Def x []      | Just x == inf -> return $ [DSizeInf]
        Def x [u]     | Just x == suc -> maxViewSuc_ (fromJust suc) <$> loop (unArg u)
        Def x [u1,u2] | Just x == max -> maxViewMax <$> loop (unArg u1) <*> loop (unArg u2)
        Var i []                      -> return $ [DSizeVar i 0]
        MetaV x us                    -> return $ [DSizeMeta x us 0]
        _                             -> return $ [DOtherSize v]
  loop v

-- | Account for subtyping @Size< i =< Size@
--   Preconditions:
--   @m = x els1@, @n = y els2@, @m@ and @n@ are not equal.
trySizeUniv :: Comparison -> Type -> Term -> Term
  -> QName -> [Elim] -> QName -> [Elim] -> TCM ()
trySizeUniv cmp t m n x els1 y els2 = do
  let failure = typeError $ UnequalTerms cmp m n t
      forceInfty u = compareSizes CmpEq (unArg u) =<< primSizeInf
  (size, sizelt) <- flip catchError (const failure) $ do
     Def size   _ <- ignoreSharing <$> primSize
     Def sizelt _ <- ignoreSharing <$> primSizeLt
     return (size, sizelt)
  case (cmp, els1, els2) of
     (CmpLeq, [_], [])  | x == sizelt && y == size -> return ()
     (_, [Apply u], []) | x == sizelt && y == size -> forceInfty u
     (_, [], [Apply u]) | x == size && y == sizelt -> forceInfty u
     _                                             -> failure

-- | Compare two sizes. Only with --sized-types.
compareSizes :: Comparison -> Term -> Term -> TCM ()
compareSizes cmp u v = do
  reportSDoc "tc.conv.size" 10 $ vcat
    [ text "Comparing sizes"
    , nest 2 $ sep [ prettyTCM u <+> prettyTCM cmp
                   , prettyTCM v
                   ]
    ]
{-
  u <- reduce u
  v <- reduce v
  reportSDoc "tc.conv.size" 15 $
      nest 2 $ sep [ text (show u) <+> prettyTCM cmp
                   , text (show v)
                   ]
-}
  us <- sizeMaxView u
  vs <- sizeMaxView v
  compareMaxViews cmp us vs

compareMaxViews :: Comparison -> SizeMaxView -> SizeMaxView -> TCM ()
compareMaxViews cmp us vs = case (cmp, us, vs) of
  (CmpLeq, _, (DSizeInf : _)) -> return ()
  (cmp,   [u], [v]) -> compareSizeViews cmp u v
  (CmpLeq, us, [v]) -> forM_ us $ \ u -> compareSizeViews cmp u v
  (CmpLeq, us, vs)  -> forM_ us $ \ u -> compareBelowMax u vs
  (CmpEq,  us, vs)  -> compareMaxViews CmpLeq us vs >> compareMaxViews CmpLeq vs us
--  _ -> typeError $ NotImplemented "compareMaxViews"

-- | @compareBelowMax u vs@ checks @u <= max vs@.  Precondition: @size vs >= 2@
compareBelowMax :: DeepSizeView -> SizeMaxView -> TCM ()
compareBelowMax u vs =
  alt (dontAssignMetas $ alts $ map (compareSizeViews CmpLeq u) vs) $ do
    u <- unDeepSizeView u
    v <- unMaxView vs
    size <- sizeType
    addConstraint $ ValueCmp CmpLeq size u v
  where alt  c1 c2 = c1 `catchError` const c2
        alts []     = __IMPOSSIBLE__
        alts [c]    = c
        alts (c:cs) = c `alt` alts cs

compareSizeViews :: Comparison -> DeepSizeView -> DeepSizeView -> TCM ()
compareSizeViews cmp s1' s2' = do
  size <- sizeType
  let (s1, s2) = removeSucs (s1', s2')
      withUnView cont = do
        u <- unDeepSizeView s1
        v <- unDeepSizeView s2
        cont u v
      failure = withUnView $ \ u v -> typeError $ UnequalTerms cmp u v size
      continue cmp = withUnView $ compareAtom cmp size
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
      unlessM (trivial u v) $ addConstraint $ ValueCmp CmpLeq size u v
    (CmpEq, s1, s2) -> continue cmp

{-
-- | Compare two sizes. Only with --sized-types.
compareSizes :: Comparison -> Term -> Term -> TCM ()
compareSizes cmp u v = do
  reportSDoc "tc.conv.size" 10 $ vcat
    [ text "Comparing sizes"
    , nest 2 $ sep [ prettyTCM u <+> prettyTCM cmp
                   , prettyTCM v
                   ]
    ]
  u <- reduce u
  v <- reduce v
  reportSDoc "tc.conv.size" 15 $
      nest 2 $ sep [ text (show u) <+> prettyTCM cmp
                   , text (show v)
                   ]
  s1'  <- deepSizeView u
  s2'  <- deepSizeView v
  size <- sizeType
  let failure = typeError $ UnequalTerms cmp u v size
      (s1, s2) = removeSucs (s1', s2')
      continue cmp = do
        u <- unDeepSizeView s1
        v <- unDeepSizeView s2
        compareAtom cmp size u v
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
         BoundedLt u' ->
            -- now we have i < u', in the worst case i+1 = u'
            -- and we want to check i+n <= v
            if n > 0 then do
              u'' <- sizeSuc (n - 1) u'
              compareSizes cmp u'' v
             else compareSizes cmp u' =<< sizeSuc 1 v
    (CmpLeq, s1,        s2)         -> do
      u <- unDeepSizeView s1
      v <- unDeepSizeView s2
      unlessM (trivial u v) $ addConstraint $ ValueCmp CmpLeq size u v
    (CmpEq, s1, s2) -> continue cmp
-}
{-
  s1   <- sizeView u
  s2   <- sizeView v
  size <- sizeType
  case (cmp, s1, s2) of
    (CmpLeq, _,         SizeInf)   -> return ()
    (CmpLeq, SizeInf,   _)         -> compareSizes CmpEq u v
    (CmpEq,  SizeSuc u, SizeInf)   -> compareSizes CmpEq u v
    (_,      SizeInf,   SizeSuc v) -> compareSizes CmpEq u v
    (_,      SizeSuc u, SizeSuc v) -> compareSizes cmp u v
    (CmpLeq, _,         _)         ->
      unlessM (trivial u v) $ addConstraint $ ValueCmp CmpLeq size u v
    _ -> compareAtom cmp size u v
-}

isBounded :: Nat -> TCM BoundedSize
isBounded i = do
  t <- reduce =<< typeOfBV i
  case ignoreSharing $ unEl t of
    Def x [u] -> do
      sizelt <- getBuiltin' builtinSizeLt
      return $ if (Just (Def x []) == sizelt) then BoundedLt $ unArg u else BoundedNo
    _ -> return BoundedNo

trivial :: Term -> Term -> TCM Bool
trivial u v = do
    a <- sizeExpr u
    b <- sizeExpr v
    let triv = case (a, b) of
          -- Andreas, 2012-02-24  filtering out more trivial constraints fixes
          -- test/lib-succeed/SizeInconsistentMeta4.agda
          ((e, n), (e', n')) -> e == e' && n <= n'
        {-
          ((Rigid i, n), (Rigid j, m)) -> i == j && n <= m
          _ -> False
        -}
    reportSDoc "tc.conv.size" 15 $
      nest 2 $ sep [ if triv then text "trivial constraint" else empty
                   , text (show a) <+> text "<="
                   , text (show b)
                   ]
    return triv
  `catchError` \_ -> return False

-- | Whenever we create a bounded size meta, add a constraint
--   expressing the bound.
--   In @boundedSizeMetaHook v tel a@, @tel@ includes the current context.
boundedSizeMetaHook :: Term -> Telescope -> Type -> TCM ()
boundedSizeMetaHook v tel0 a = do
  res <- isSizeType a
  case res of
    Just (BoundedLt u) -> do
      n <- getContextSize
      let tel | n > 0     = telFromList $ genericDrop n $ telToList tel0
              | otherwise = tel0
      addCtxTel tel $ do
        v <- sizeSuc 1 $ raise (size tel) v `apply` teleArgs tel
        -- compareSizes CmpLeq v u
        size <- sizeType
        addConstraint $ ValueCmp CmpLeq size v u
    _ -> return ()

-- | Test whether a problem consists only of size constraints.
isSizeProblem :: ProblemId -> TCM Bool
isSizeProblem pid = andM . map (isSizeConstraint . theConstraint) =<< getConstraintsForProblem pid

-- | Test is a constraint speaks about sizes.
isSizeConstraint :: Closure Constraint -> TCM Bool
isSizeConstraint (Closure{ clValue = ValueCmp _ s _ _ }) = isJust <$> isSizeType s
isSizeConstraint _ = return False

-- | Find the size constraints.
getSizeConstraints :: TCM [Closure Constraint]
getSizeConstraints = do
  cs   <- getAllConstraints
  test <- isSizeTypeTest
  let sizeConstraint cl@Closure{ clValue = ValueCmp CmpLeq s _ _ }
              | isJust (test s) = Just cl
      sizeConstraint _ = Nothing
  return $ mapMaybe (sizeConstraint . theConstraint) cs

getSizeMetas :: TCM [(MetaId, Int)]
getSizeMetas = do
  ms <- getOpenMetas
  test <- isSizeTypeTest
  let sizeCon m = do
        let nothing  = return []
        mi <- lookupMeta m
        case mvJudgement mi of
          HasType _ a -> do
            TelV tel b <- telView =<< instantiateFull a
            case test b of
              Nothing -> nothing
              Just _  -> return [(m, size tel)]
          _ -> nothing
  concat <$> mapM sizeCon ms

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
                (b, n) <- sizeExpr u
                return ([(m, size tel)], [Leq a (n-1) b])
-}
          _ -> nothing
  (mss, css) <- unzip <$> mapM sizeCon ms
  return (concat mss, concat css)
-}

-- | Atomic size expressions.
data SizeExpr
  = SizeMeta MetaId [Int] -- ^ A size meta applied to de Bruijn levels.
  | Rigid Int             -- ^ A de Bruijn level.
  deriving (Eq)

instance Show SizeExpr where
  show (SizeMeta m _) = "X" ++ show (fromIntegral m :: Int)
  show (Rigid i)      = "c" ++ show (fromIntegral i :: Int)

-- | Size constraints we can solve.
data SizeConstraint
  = Leq SizeExpr Int SizeExpr -- ^ @Leq a +n b@ represents @a =< b + n@.
                              --   @Leq a -n b@ represents @a + n =< b@.

instance Show SizeConstraint where
  show (Leq a n b)
    | n == 0    = show a ++ " =< " ++ show b
    | n > 0     = show a ++ " =< " ++ show b ++ " + " ++ show n
    | otherwise = show a ++ " + " ++ show (-n) ++ " =< " ++ show b

-- | Compute a set of size constraints that all live in the same context
--   from constraints over terms of type size that may live in different
--   contexts.
--
--   cf. 'Agda.TypeChecking.LevelConstraints.simplifyLevelConstraint'
computeSizeConstraints :: [Closure Constraint] -> TCM [SizeConstraint]
computeSizeConstraints [] = return [] -- special case to avoid maximum []
computeSizeConstraints cs = do
  scs <- mapM computeSizeConstraint leqs
  return [ c | Just c <- scs ]
  where
    -- get the constraints plus contexts they are defined in
    unClosure cl = (envContext $ clEnv cl, clValue cl)
    (gammas, ls) = unzip $ map unClosure cs
    -- compute the longest context (common water level)
    gamma        = maximumBy (compare `on` size) gammas
    waterLevel   = size gamma
    -- convert deBruijn indices to deBruijn levels to
    -- enable comparing constraints under different contexts
    leqs = zipWith raise (map ((waterLevel -) . size) gammas) ls

-- | Turn a constraint over de Bruijn levels into a size constraint.
computeSizeConstraint :: Constraint -> TCM (Maybe SizeConstraint)
computeSizeConstraint c = case c of
      ValueCmp CmpLeq _ u v -> do
          reportSDoc "tc.size.solve" 50 $ sep
            [ text "converting size constraint"
            , prettyTCM c
            ]
          (a, n) <- sizeExpr u
          (b, m) <- sizeExpr v
          return $ Just $ Leq a (m - n) b
        `catchError` \err -> case err of
          PatternErr _ -> return Nothing
          _            -> throwError err
      _ -> __IMPOSSIBLE__

-- | Turn a term with de Bruijn levels into a size expression with offset.
--
--   Throws a 'patternViolation' if the term isn't a proper size expression.
sizeExpr :: Term -> TCM (SizeExpr, Int)
sizeExpr u = do
  u <- reduce u -- Andreas, 2009-02-09.
                -- This is necessary to surface the solutions of metavariables.
  reportSDoc "tc.conv.size" 60 $ text "sizeExpr:" <+> prettyTCM u
  s <- sizeView u
  case s of
    SizeInf     -> patternViolation
    SizeSuc u   -> mapSnd (+1) <$> sizeExpr u
    OtherSize u -> case ignoreSharing u of
      Var i []  -> return (Rigid i, 0)  -- i is already a de Bruijn level.
      MetaV m args | Just xs <- mapM isVar args, fastDistinct xs
                -> return (SizeMeta m xs, 0)
      _ -> patternViolation
  where
    isVar v = case ignoreSharing $ unArg v of
      Var i [] -> Just i
      _        -> Nothing

-- | Compute list of size metavariables with their arguments
--   appearing in a constraint.
flexibleVariables :: SizeConstraint -> [(MetaId, [Int])]
flexibleVariables (Leq a _ b) = flex a ++ flex b
  where
    flex (Rigid _)       = []
    flex (SizeMeta m xs) = [(m, xs)]

haveSizedTypes :: TCM Bool
haveSizedTypes = do
    Def _ [] <- ignoreSharing <$> primSize
    Def _ [] <- ignoreSharing <$> primSizeInf
    Def _ [] <- ignoreSharing <$> primSizeSuc
    optSizedTypes <$> pragmaOptions
  `catchError` \_ -> return False

solveSizeConstraints :: TCM ()
solveSizeConstraints = whenM haveSizedTypes $ do
  reportSLn "tc.size.solve" 70 $ "Considering to solve size constraints"
  cs0 <- getSizeConstraints
  cs <- computeSizeConstraints cs0
  ms <- getSizeMetas
{- ROLLED BACK
  cs0 <- getSizeConstraints
  cs1 <- computeSizeConstraints cs0
  (ms,cs2) <- getSizeMetas
  let cs = cs2 ++ cs1
-}
  when (not (null cs) || not (null ms)) $ do
  reportSLn "tc.size.solve" 10 $ "Solving size constraints " ++ show cs

  let -- Error for giving up
      cannotSolve = typeError . GenericDocError =<<
        vcat (text "Cannot solve size constraints" : map prettyTCM cs0)

      -- Ensure that each occurrence of a meta is applied to the same
      -- arguments ("flexible variables").
      mkMeta :: [(MetaId, [Int])] -> TCM (MetaId, [Int])
      mkMeta ms@((m, xs) : _)
        | allEqual (map snd ms) = return (m, xs)
        | otherwise             = do
            reportSLn "tc.size.solve" 20 $
              "Size meta variable " ++ show m ++ " not always applied to same arguments: " ++ show (nub (map snd ms))
            cannotSolve
      mkMeta _ = __IMPOSSIBLE__

  metas0 <- mapM mkMeta $ groupOn fst $ concatMap flexibleVariables cs


  let mkFlex (m, xs) = W.NewFlex (fromIntegral m) $ \i -> fromIntegral i `elem` xs

      mkConstr (Leq a n b)  = W.Arc (mkNode a) n (mkNode b)
      mkNode (Rigid i)      = W.Rigid $ W.RVar $ fromIntegral i
      mkNode (SizeMeta m _) = W.Flex $ fromIntegral m

      found (m, _) = elem m $ map fst metas0

  -- Compute unconstrained metas
  let metas1 = map mkMeta' $ filter (not . found) ms
      mkMeta' (m, n) = (m, [0..fromIntegral n - 1])

  let metas = metas0 ++ metas1

  reportSLn "tc.size.solve" 15 $ "Metas: " ++ show metas0 ++ ", " ++ show metas1

  verboseS "tc.size.solve" 20 $
      -- debug print the type of all size metas
      forM_ metas $ \ (m, _) ->
          reportSDoc "" 0 $ prettyTCM =<< mvJudgement <$> lookupMeta m

  -- run the Warshall solver
  case W.solve $ map mkFlex metas ++ map mkConstr cs of
    Nothing  -> cannotSolve
    Just sol -> do
      reportSLn "tc.size.solve" 10 $ "Solved constraints: " ++ show sol
      s <- primSizeSuc
      let suc v = s `apply` [defaultArg v]
          plus v 0 = v
          plus v n = suc $ plus v (n - 1)

          inst (i, e) = do

            let m = fromIntegral i  -- meta variable identifier

                args = case lookup m metas of
                  Just xs -> xs
                  Nothing -> __IMPOSSIBLE__

                isInf (W.SizeConst W.Infinite) = True
                isInf _                        = False

                term (W.SizeConst (W.Finite _)) = __IMPOSSIBLE__
                term (W.SizeConst W.Infinite) = primSizeInf
                term (W.SizeVar j n) = case findIndex (==fromIntegral j) $ reverse args of
                  Just x -> return $ plus (var x) n
                  Nothing -> __IMPOSSIBLE__

                lam _ v = Lam NotHidden $ Abs "s" v

            b <- term e
            let v = foldr lam b args -- TODO: correct hiding

            reportSDoc "tc.size.solve" 20 $ sep
              [ text (show m) <+> text ":="
              , nest 2 $ prettyTCM v
              ]

            -- Andreas, 2012-09-25: do not assign interaction metas to \infty
            unlessM (isInteractionMeta m `and2M` return (isInf e)) $
              assignTerm m v

      mapM_ inst $ Map.toList sol

      -- Andreas, 2012-09-19
      -- The returned solution might not be consistent with
      -- the hypotheses on rigid vars (j : Size< i).
      -- Thus, we double check that all size constraints
      -- have been solved correctly.
      flip catchError (const cannotSolve) $
        noConstraints $
          forM_ cs0 $ \ cl -> enterClosure cl solveConstraint
