{-# OPTIONS_GHC -fwarn-unused-imports -fwarn-name-shadowing #-}
module Agda.Compiler.Epic.Optimize where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe

import Agda.Syntax.Internal(QName)
import qualified Agda.Syntax.Internal as T
import Agda.TypeChecking.Monad hiding (defName)
import Agda.TypeChecking.Monad.Builtin

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState
import Agda.Compiler.Epic.NatDetection

#include "../../undefined.h"
import Agda.Utils.Impossible

{- Stacken, Heapen -- Optimizern -}


-- Map QName (Expr -> Expr)

data PrimTransform = PrimTF
  { mapCon        :: Map QName Var
  , translateCase :: Expr -> [Branch] -> Expr
  }

transformBuiltins :: MonadTCM m => [Fun] -> Compile m [Fun]
transformBuiltins funs = do
    liftIO $ putStrLn "starting OPT.builtins"
    ptfs <- getBuiltins
    natish <- getNatish
    liftIO $ putStrLn $ "NATISH: " ++ show natish
    mapM (translateFun $ ptfs ++ map (uncurry natPrimTF) natish) funs

getBuiltins :: MonadTCM m => Compile m [PrimTransform]
getBuiltins =
    catMaybes <$> sequence
      [ [builtinZero, builtinSuc  ] ~> natPrimTF [True]
       -- ? is this ok to have [True]
      , [builtinLevelZero, builtinLevelSuc] ~> natPrimTF [True]
      , [builtinTrue, builtinFalse] ~> boolPrimTF
      ]
  where
    constrs ~> transf = do
        builtins <- lift $ mapM getBuiltin' constrs
        if all isJust builtins
           then return $ Just (transf (map (defName . fromMaybe __IMPOSSIBLE__) builtins))
           else return Nothing
    defName (T.Def q []) = q
    defName (T.Con q []) = q
    defName x            = error $ show x

natPrimTF :: IrrFilter -> [QName] -> PrimTransform
natPrimTF filt [zero, suc] = PrimTF
  { mapCon = M.fromList [(zero, "primZero"), (suc, "primSuc")]
  , translateCase = \ce brs -> case brs of
        [Branch _ n vs e, Branch _ n' vs' e'] ->
            if n == zero
               then primNatCaseZS ce e  (head (pairwiseFilter filt vs')) e'
               else primNatCaseZS ce e' (head (pairwiseFilter filt vs )) e
        [Branch _ n vs e, Default e'] ->
            if n == zero
               then primNatCaseZD ce e e'    -- zero
               else primNatCaseZS ce e' (head (pairwiseFilter filt vs )) e  -- suc (IMPORTANT PRIMES, BE CAREFUL)
        _ -> __IMPOSSIBLE__
  }
natPrimTF _ _ = __IMPOSSIBLE__

primNatCaseZS n zeroBr v sucBr =
    If (App "primNatEquality" [n, Var "primZero"]) zeroBr (Let v (App "primPred" [n]) sucBr)
primNatCaseZD n zeroBr defBr = If (App "primNatEquality" [n, Var "primZero"]) zeroBr defBr


boolPrimTF :: [QName] -> PrimTransform
boolPrimTF [true, false] = PrimTF
  { mapCon = M.fromList [(true, "primTrue"), (false, "primFalse")]
  , translateCase = \ce brs ->
    case brs of
        [Branch _ n vs e, b'] ->
                    (if n == true
                             then If ce e (brExpr b')
                             else If ce (brExpr b') e)
        _ -> __IMPOSSIBLE__
  }
boolPrimTF _ = __IMPOSSIBLE__

translateFun :: MonadIO m => [PrimTransform] -> Fun -> Compile m Fun
translateFun ptfs (Fun i n c args e) =
    Fun i n c args <$> translate ptfs e
translateFun _ e@(EpicFun {}) = return e

translate :: MonadIO m => [PrimTransform] -> Expr -> Compile m Expr
translate prim ex = case ex of
    Var{}    -> return ex
    Lit{}    -> return ex
    Lam v e1 -> Lam v <$> translate prim e1
    Con c n es -> case testCon prim n of
        Just pn -> do
            filt <- getIrrFilter n
            apps pn <$> mapM (translate prim) (pairwiseFilter filt es)
        Nothing -> Con c n <$> mapM (translate prim) es
    App v es   -> App v <$> mapM (translate prim) es
    Case e brs -> case testBranch prim brs of
       Just p  -> do
          liftIO $ putStrLn $ "translateCase: " ++ show ex
          translate prim $ translateCase p e brs
       Nothing -> Case <$> translate prim e <*> mapM translateBranch brs
    If a b c   -> If <$> translate prim a <*> translate prim b <*> translate prim c
    Let v e e' -> Let v <$> translate prim e <*> translate prim e'
    Lazy e     -> Lazy <$> translate prim e
    UNIT       -> return ex
    IMPOSSIBLE -> return ex
  where
    testCon :: [PrimTransform] -> QName -> Maybe Var
    testCon [] _ = Nothing
    testCon (p : ps) k = M.lookup k (mapCon p) `mplus` testCon ps k

    testBranch :: [PrimTransform] -> [Branch] -> Maybe PrimTransform
    testBranch [] _       = Nothing
    testBranch (p:ps) brs = msum (map (check p) brs) `mplus` testBranch ps brs

    check :: PrimTransform -> Branch -> Maybe PrimTransform
    check p br = case br of
        Branch  _ n _ _ -> fmap (const p) $ M.lookup n (mapCon p)
        BrInt _ _       -> Nothing
        Default _       -> Nothing

    translateBranch :: MonadIO m => Branch -> Compile m Branch
    translateBranch br = do
        e' <- translate prim (brExpr br)
        return br {brExpr = e'}
