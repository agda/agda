{-# LANGUAGE CPP #-}
module Agda.TypeChecking.SizedTypes where

import Control.Monad.Error
import Control.Monad
import Data.List
import qualified Data.Map as Map

import Agda.Interaction.Options
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import qualified Agda.Utils.Warshall as W
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Impossible
import Agda.Utils.Size

#include "../undefined.h"

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
      ifM (trivial u v) (return ()) $
        addConstraint $ ValueCmp CmpLeq size u v
    _ -> compareAtom cmp size u v

trivial :: Term -> Term -> TCM Bool
trivial u v = liftTCM $ do
    a <- sizeExpr u
    b <- sizeExpr v
    reportSDoc "tc.conv.size" 15 $
      nest 2 $ sep [ text (show a) <+> text "<="
                   , text (show b)
                   ]
    return $ case (a, b) of
      ((Rigid i, n), (Rigid j, m)) -> i == j && n <= m
      _ -> False
  `catchError` \_ -> return False

-- | Find the size constraints.
getSizeConstraints :: TCM [SizeConstraint]
getSizeConstraints = do
  cs   <- getAllConstraints
  size <- sizeType
  let sizeConstraints cl@(Closure{ clValue = ValueCmp CmpLeq s _ _ })
        | s == size = [cl]
      sizeConstraints _ = []
  scs <- mapM computeSizeConstraint $ concatMap (sizeConstraints . theConstraint) cs
  return [ c | Just c <- scs ]

getSizeMetas :: TCM [(MetaId, Int)]
getSizeMetas = do
  ms <- getOpenMetas
  sz <- sizeType
  let sizeCon m = do
        mi <- lookupMeta m
        case mvJudgement mi of
          HasType _ a -> do
            TelV tel b <- telView =<< instantiateFull a
            if b /= sz
              then return []
              else return [(m, size tel)]
          _ -> return []
  concat <$> mapM sizeCon ms

data SizeExpr = SizeMeta MetaId [CtxId]
              | Rigid CtxId

-- Leq a n b = (a =< b + n)
data SizeConstraint = Leq SizeExpr Int SizeExpr

instance Show SizeExpr where
  show (SizeMeta m _) = "X" ++ show (fromIntegral m :: Int)
  show (Rigid i) = "c" ++ show (fromIntegral i :: Int)

instance Show SizeConstraint where
  show (Leq a n b)
    | n == 0    = show a ++ " =< " ++ show b
    | n > 0     = show a ++ " =< " ++ show b ++ " + " ++ show n
    | otherwise = show a ++ " + " ++ show (-n) ++ " =< " ++ show b

computeSizeConstraint :: Closure Constraint -> TCM (Maybe SizeConstraint)
computeSizeConstraint cl = liftTCM $
  enterClosure cl $ \c ->
    case c of
      ValueCmp CmpLeq _ u v -> do
          (a, n) <- sizeExpr u
          (b, m) <- sizeExpr v
          return $ Just $ Leq a (m - n) b
        `catchError` \err -> case errError err of
          PatternErr _ -> return Nothing
          _            -> throwError err
      _ -> __IMPOSSIBLE__

-- | Throws a 'patternViolation' if the term isn't a proper size expression.
sizeExpr :: Term -> TCM (SizeExpr, Int)
sizeExpr u = do
  u <- reduce u -- Andreas, 2009-02-09.
                -- This is necessary to surface the solutions of metavariables.
  s <- sizeView u
  case s of
    SizeSuc u -> do
      (e, n) <- sizeExpr u
      return (e, n + 1)
    SizeInf -> patternViolation
    OtherSize u -> case u of
      Var i []  -> do
        cxt <- getContextId
        return (Rigid (cxt !! fromIntegral i), 0)
      MetaV m args
        | all isVar args && distinct args -> do
          cxt <- getContextId
          return (SizeMeta m [ cxt !! fromIntegral i | Arg _ _ (Var i []) <- args ], 0)
      _ -> patternViolation
  where
    isVar (Arg _ _ (Var _ [])) = True
    isVar _ = False

flexibleVariables :: SizeConstraint -> [(MetaId, [CtxId])]
flexibleVariables (Leq a _ b) = flex a ++ flex b
  where
    flex (Rigid _)       = []
    flex (SizeMeta m xs) = [(m, xs)]

haveSizedTypes :: TCM Bool
haveSizedTypes = liftTCM $ do
    Def _ [] <- primSize
    Def _ [] <- primSizeInf
    Def _ [] <- primSizeSuc
    optSizedTypes <$> pragmaOptions
  `catchError` \_ -> return False

solveSizeConstraints :: TCM ()
solveSizeConstraints = whenM haveSizedTypes $ do
  cs <- getSizeConstraints
  ms <- getSizeMetas
  when (not (null cs) || not (null ms)) $ do
  reportSLn "tc.size.solve" 10 $ "Solving size constraints " ++ show cs

  let metas0 = map mkMeta $ groupOn fst $ concatMap flexibleVariables cs
      mkMeta ms@((m, xs) : _)
        | allEqual (map snd ms) = (m, xs)
        | otherwise             = error $ "Inconsistent meta: " ++ show m ++ " " ++ show (map snd ms)
      mkMeta _ = __IMPOSSIBLE__

      mkFlex (m, xs) = W.NewFlex (fromIntegral m) $ \i -> fromIntegral i `elem` xs

      mkConstr (Leq a n b)  = W.Arc (mkNode a) n (mkNode b)
      mkNode (Rigid i)      = W.Rigid $ W.RVar $ fromIntegral i
      mkNode (SizeMeta m _) = W.Flex $ fromIntegral m

      found (m, _) = elem m $ map fst metas0

  -- Compute unconstrained metas
  let metas1 = map mkMeta' $ filter (not . found) ms
      mkMeta' (m, n) = (m, [0..fromIntegral n - 1])

  let metas = metas0 ++ metas1

  reportSLn "tc.size.solve" 15 $ "Metas: " ++ show metas0 ++ ", " ++ show metas1

  verboseS "tc.size.solve" 20 $ do
    let meta (m, _) = do
          j <- mvJudgement <$> lookupMeta m
          reportSDoc "" 0 $ prettyTCM j
    mapM_ meta metas

  case W.solve $ map mkFlex metas ++ map mkConstr cs of
    Nothing  -> do
      typeError $ GenericError $ "Unsolvable size constraints: " ++ show cs
    Just sol -> do
      reportSLn "tc.size.solve" 10 $ "Solved constraints: " ++ show sol
      inf <- primSizeInf
      s <- primSizeSuc
      let suc v = s `apply` [defaultArg v]
          plus v 0 = v
          plus v n = suc $ plus v (n - 1)

          inst (i, e) = do
            let m = fromIntegral i
                args = case lookup m metas of
                  Just xs -> xs
                  Nothing -> __IMPOSSIBLE__

                term (W.SizeConst (W.Finite _)) = __IMPOSSIBLE__
                term (W.SizeConst W.Infinite) = primSizeInf
                term (W.SizeVar j n) = case findIndex (==fromIntegral j) $ reverse args of
                  Just x -> return $ plus (Var (fromIntegral x) []) n
                  Nothing -> __IMPOSSIBLE__

                lam _ v = Lam NotHidden $ Abs "s" v

            b <- term e
            let v = foldr lam b args -- TODO: correct hiding

            reportSDoc "tc.size.solve" 20 $ sep
              [ text (show m) <+> text ":="
              , nest 2 $ prettyTCM v
              ]

            assignTerm m v

      mapM_ inst $ Map.toList sol

-- type Solution = Map Int SizeExpr
-- data SizeExpr = SizeVar Int Int   -- e.g. x + 5
--               | SizeConst Weight  -- a number or infinity
-- data Weight = Finite Int | Infinite
-- data Node = Rigid Rigid
--           | Flex  FlexId
-- data Rigid = RConst Weight
--            | RVar RigidId
