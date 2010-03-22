

{-# OPTIONS -fglasgow-exts -XUndecidableInstances #-}

module Agda.Auto.SearchControl where

import Agda.Utils.Impossible
-- mode: Agda implicit arguments
-- mode: Omitted arguments, used for implicit constructor type arguments
-- mode: A sort can be unknown, used as a hack for Agda's universe polymorphism
import Control.Monad
import Data.IORef
import Control.Monad.State
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax




filterMap :: (a -> Maybe b) -> [a] -> [b]
filterMap f = iter
 where iter [] = []
       iter (x:xs) = let xs' = iter xs
                     in case f x of
                          Nothing -> xs'
                          Just x' -> x' : xs'


instance Refinable (ArgList o) (RefInfo o) where
 refinements _ infos _ =
  return $ [
            (0, return ALNil),

            (0, cons NotHidden),
            (0, cons Hidden)
           ]
  where cons hid = do p1 <- newPlaceholder
                      p2 <- newPlaceholder
                      return $ ALCons hid p1 p2
getinfo = f Nothing [] False False Nothing Nothing False
 where
  f (Just x) us inf eli used is pss [] = (x, us, inf, eli, used, is, pss)
  f Nothing us inf eli used is pss (x@RIMainInfo{} : xs) = f (Just x) us inf eli used is pss xs
  f m us inf eli used is pss (x@RIUnifInfo{} : xs) = f m (x : us) inf eli used is pss xs
  f m us _ eli used is pss (RIInferredTypeUnknown : xs) = f m us True eli used is pss xs
  f m us inf _ used is pss (RINotConstructor : xs) = f m us inf True used is pss xs
  f m us inf eli used is pss (RIUsedVars nuids nused : xs) =
   f m us inf eli (Just (nuids, nused)) is pss xs
  f m us inf eli used Nothing pss (RIIotaStep semif : xs) = f m us inf eli used (Just semif) pss xs
  f m us inf eli used (Just osemif) pss (RIIotaStep semif : xs) = f m us inf eli used (Just $ osemif || semif) pss xs
  f m us inf eli used is _ (RIPickSubsvar : xs) = f m us inf eli used is True xs
  f _ _ _ _ _ _ _ _ = (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/SearchControl.hs") 60))
univar :: [CAction o] -> Nat -> Maybe Nat
univar cl v = f cl v 0
 where
 f [] v v' = Just (v' + v)
 f (Weak n : _) v v' | v < n = Nothing
 f (Weak n : xs) v v' = f xs (v - n) v'
 f (Sub _ : xs) v v' = f xs v (v' + 1)
 f (Skip : _) 0 v' = Just v'
 f (Skip : xs) v v' = f xs (v - 1) (v' + 1)
subsvars :: [CAction o] -> [Nat]
subsvars = f 0
 where
  f n [] = []
  f n (Weak _ : xs) = f n xs
  f n (Sub _ : xs) = n : f (n + 1) xs
  f n (Skip : xs) = f (n + 1) xs
instance Refinable (Exp o) (RefInfo o) where
 refinements envinfo infos meta =
  let
   RIEnv hints = envinfo
   (RIMainInfo n tt iotastepdone, unis, inftypeunknown, iseliminand, Just (uids, usedvars), iotastep, picksubsvar) = getinfo infos
   app muid elr = do p <- newPlaceholder
                     okh <- newOKHandle
                     let uid = case muid of
                                Just _ -> muid
                                Nothing -> Just meta
                     return $ App uid okh elr p
   lam hid id = do
    p <- newPlaceholder
    return $ Lam hid (Abs id p)
   pi muid dep hid =
    do p1 <- newPlaceholder
       p2 <- newPlaceholder
       let uid = case muid of
                  Just _ -> muid
                  Nothing -> Just meta
       return $ Pi uid hid dep p1 (Abs NoId p2)
   set l = return $ Sort (Set l)
  in case unis of
   [] ->
    let
     pcav i = if inftypeunknown then costInferredTypeUnkown else i
     pc i = pcav i
     varapps = map (\v ->
                (pcav (case Just usedvars of {Just usedvars -> if elem v usedvars then costAppVarUsed else costAppVar; Nothing -> if picksubsvar then costAppVar else costAppVarUsed}),
                 app Nothing (Var v)
                )) [0..n - 1]
     hintapps = map (\c ->
                 (cost,
                  app Nothing (Const c)
                 )) hints
                 where cost = pc (case iotastep of {Just _ -> costIotaStep; Nothing -> costAppHint})
     generics = varapps ++ hintapps
    in case tt of
     HNPi _ hid possdep _ (Abs id _) -> return $ (pc (if iotastepdone then costLamUnfold else costLam), lam hid id) : (costAbsurdLam, return $ AbsurdLambda hid) : generics
     HNSort (Set l) -> return $ map (\l -> (pc costSort, set l)) [0..l - 1] ++ [(pc costPi, pi Nothing True NotHidden), (pc costPi, pi Nothing True Hidden)] ++ generics
     HNApp _ (Const c) _ -> do
      cd <- readIORef c
      return $ case cdcont cd of
       Datatype cons -> map (\c -> (pc (case iotastep of {Just True -> costUnification; _ -> if length cons <= 1 then costAppConstructorSingle else costAppConstructor}), app Nothing (Const c))) cons ++ generics
       _ -> generics
     _ -> return generics
   (RIUnifInfo cl hne : _) ->
    let
     subsvarapps = map (\v ->
                    (costUnification,
                     app Nothing (Var v)
                    )) (subsvars cl)
     mlam = case tt of
      HNPi _ hid _ _ (Abs id _) -> [(costUnification, lam hid id)]
      _ -> []
     generics = mlam ++ subsvarapps
     checkocc uid = case uid of {Just uid | elem uid uids -> costUnificationOccurs; _ -> costUnification}
    in
     return $ case hne of
      HNApp uid (Var v) _ ->
       let uni = case univar cl v of
                  Just v | v < n -> [(checkocc uid, app uid (Var v))]
                  _ -> []
       in uni ++ generics
      HNApp uid (Const c) _ -> (checkocc uid, app uid (Const c)) : generics
      HNLam{} -> generics
      HNPi uid hid possdep _ _ -> (checkocc uid, pi uid possdep hid) : generics
      HNSort (Set l) -> map (\l -> (costUnification, set l)) [0..l] ++ generics
      HNSort _ -> generics
   _ -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/SearchControl.hs") 155))
extraref meta uid c = (costAppExtraRef, app uid (Const c))
 where
   app muid elr = do p <- newPlaceholder
                     okh <- newOKHandle
                     let uid = case muid of
                                Just _ -> muid
                                Nothing -> Just meta
                     return $ App uid okh elr p
-- ---------------------------------
-- ---------------------------------
costIotaStep, costAppExtraRef, costIncrease :: Int
costIncrease = 1000
costUnificationOccurs = 1000001 -- 1 -- 100
costUnification = 0000
costAppVar = 0000 -- 0, 1
costAppVarUsed = 1000 -- 5
costAppHint = 3000 -- 2, 5
costAppConstructor = 1000
costAppConstructorSingle = 0000
costAppExtraRef = 1000
costLam = 0000 -- 1, 0
costLamUnfold = 1000 -- 1, 0
costPi = 1000003 -- 100 -- 5
costSort = 1000004 -- 0
costIotaStep = 3000 -- 1000005 -- 2 -- 100
costInferredTypeUnkown = 1000006 -- 100
costAbsurdLam = 0
prioNo, prioTypeUnknown, prioTypecheckArgList, prioInferredTypeUnknown, prioCompBeta, prioCompareArgList, prioCompIota, prioCompChoice, prioCompUnif, prioNoIota, prioAbsurdLambda :: Int
prioNo = (-1)
prioTypeUnknown = 0
prioTypecheck False = 1000
prioTypecheck True = 0
prioTypecheckArgList = 3000
prioInferredTypeUnknown = 4000
prioCompBeta = 4000
prioCompIota = 4000
prioCompChoice = 5000 -- 700 -- 5000
prioCompUnif = 6000 -- 2
prioCompareArgList = 7000 -- 5 -- 2
prioNoIota = 500 -- 500
prioAbsurdLambda = 1000
-- ---------------------------------
instance Trav a blk => Trav [a] blk where
 traverse _ [] = return ()
 traverse f (x:xs) = traverse f x >> traverse f xs
instance Trav (MId, CExp o) (RefInfo o) where
 traverse f (_, ce) = traverse f ce
instance Trav (TrBr a o) (RefInfo o) where
 traverse f (TrBr es _) = traverse f es
instance Trav (Exp o) (RefInfo o) where
 traverse f e = case e of
  App _ _ _ args -> traverse f args
  Lam _ (Abs _ b) -> traverse f b
  Pi _ _ _ it (Abs _ ot) -> traverse f it >> traverse f ot
  Sort _ -> return ()
  AbsurdLambda{} -> return ()
instance Trav (ArgList o) (RefInfo o) where
 traverse _ ALNil = return ()
 traverse f (ALCons _ arg args) = traverse f arg >> traverse f args
 traverse f (ALConPar args) = traverse f args
-- ---------------------------------
