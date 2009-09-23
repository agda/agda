{-# OPTIONS -fglasgow-exts -XUndecidableInstances #-}

module Agda.Auto.SearchControl where

import Control.Monad
import Data.IORef
import Control.Monad.State

import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax
import Agda.Auto.Print


instance Refinable (ArgList o) (RefInfo o) where
 refinements _ _ = return [
   (0, return ALNil),
   (0, cons NotHidden),
   (0, cons Hidden)
  ]
  where cons hid = do p1 <- newPlaceholder
                      p2 <- newPlaceholder
                      return $ ALCons hid p1 p2
 printref x = pargs [] (NotM x)


getinfo [] (Just x) us = (x, us)
getinfo (x@(RIMainInfo _ _) : xs) Nothing us = getinfo xs (Just x) us
getinfo (x@(RIUnifInfo _ _ _) : xs) m us = getinfo xs m (x : us)
getinfo _ _ _ = error "getinfo: case should not occur"

instance Refinable (Exp o) (RefInfo o) where
 refinements envinfo infos = do
  let RIEnv hints = envinfo
      (RIMainInfo n tt, unis) = getinfo infos Nothing []
  occs <- mapM (\(RIUnifInfo mm _ opphne) -> occursCheck mm opphne) unis
  cons <- case tt of
           HNApp (Const c) _ -> do
            cd <- readIORef c
            return $ case cdcont cd of
             Datatype cons -> cons
             _ -> []
           _ -> return []
  let up = case unis of
            [] -> False
            _ -> all not occs
      lam hid = (0,
                 do p <- newPlaceholder
                    return $ Lam hid (Abs NoId p)
                )
      apps = map app [0..n - 1]
      capps = case unis of
               [] -> map capp (hints ++ cons)
               _ -> []
      app v = (if up then 0 else 1,
               do p <- newPlaceholder
                  return $ App (Var v) p
              )
      capp c = (if up then 0 else 2,
                do p <- newPlaceholder
                   return $ App (Const c) p
               )
      set l = map (\l -> (0, return $ Sort (SortLevel l))) [0 .. l - 1]
      fun hid = (2,
                 do p1 <- newPlaceholder
                    p2 <- newPlaceholder
                    return $ Fun hid p1 p2)
      pi hid = (2,
                do p1 <- newPlaceholder
                   p2 <- newPlaceholder
                   return $ Pi hid True p1 (Abs NoId p2))
      mimic = case unis of
               [] -> []
               (RIUnifInfo _ cl hnopp : _) -> case hnopp of
                HNApp (Const c) _ -> [capp c]
                _ -> []
               _ -> error "refinements: mimic: not matched"
  case tt of
   HNFun hid _ _ -> return $ lam hid : apps ++ capps ++ mimic
   HNPi hid _ _ _ -> return $ lam hid : apps ++ capps ++ mimic
   HNSort (SortLevel l) -> return $ set l ++ [fun NotHidden, fun Hidden, pi NotHidden, pi Hidden] ++ apps ++ capps ++ mimic
   _ -> return $ apps ++ capps ++ mimic
 printref x = printExp [] (NotM x)

-- ---------------------------------

occursCheck :: forall a o . Metavar a (RefInfo o) -> HNExp o -> IO Bool
occursCheck m0 hn = liftM snd $ runStateT (
  let f :: forall b . Trav b (RefInfo o) => MM b (RefInfo o) -> StateT Bool IO ()
      f (NotM x) = traverse f x
      f (Meta m) = do
         bind <- lift $ readIORef $ mbind m
         case bind of
          Just x -> traverse f x
          Nothing -> when (hequalMetavar m m0) $ put True
  in  traverse f hn
 ) False


-- ---------------------------------

prioNo, prioTypeUnknown, prioTypecheckArgList, prioInferredTypeUnknown, prioPreCompare, prioCompare, prioCompareArgList, prioCompIota, prioCompChoice :: Int
prioNo = (-1)
prioTypeUnknown = 0
prioTypecheck False = 1
prioTypecheck True = 0
prioTypecheckArgList = 3
prioInferredTypeUnknown = 4
prioPreCompare = 4
prioCompChoice = 4
prioCompare = 2
prioCompareArgList = 2
prioCompIota = 4

-- ---------------------------------

instance Trav a blk => Trav [a] blk where
 traverse _ [] = return ()
 traverse f (x:xs) = traverse f x >> traverse f xs

instance Trav (MId, CExp o) (RefInfo o) where
 traverse f (_, ce) = traverse f ce

instance Trav a (RefInfo o) => Trav (Clos a o) (RefInfo o) where
 traverse f (Clos cl e) = traverse f cl >> traverse f e

instance Trav (CAction o) (RefInfo o) where
 traverse f (Sub ce) = traverse f ce
 traverse _ Skip = return ()
 traverse _ (Weak _) = return ()

instance Trav (Exp o) (RefInfo o) where
 traverse f e = case e of
  App _ args -> traverse f args
  Lam _ (Abs _ b) -> traverse f b
  Fun _ it ot -> traverse f it >> traverse f ot
  Pi _ _ it (Abs _ ot) -> traverse f it >> traverse f ot
  Sort _ -> return ()

instance Trav (ArgList o) (RefInfo o) where
 traverse _ ALNil = return ()
 traverse f (ALCons _ arg args) = traverse f arg >> traverse f args
 traverse f (ALConPar args) = traverse f args

instance Trav (HNExp o) (RefInfo o) where
 traverse f e = case e of
  HNApp _ args -> traverse f args
  HNLam (Abs _ b) -> traverse f b
  HNFun _ it ot -> traverse f it >> traverse f ot
  HNPi _ _ it (Abs _ ot) -> traverse f it >> traverse f ot
  HNSort _ -> return ()

instance Trav (CArgList o) (RefInfo o) where
 traverse _ CALNil = return ()
 traverse f (CALConcat arg args) = traverse f arg >> traverse f args


