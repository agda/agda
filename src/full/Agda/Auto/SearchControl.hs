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
      {-set 0 = []
      -- set l = [return $ Sort (SortLevel (l - 1))]
      set l = [do p <- newPlaceholder
                  return $ Tagged (CMGuessed, error "no uid") $ Pi (NotM (Tagged (CMGuessed, error "no uid") $ Sort (SortLevel (l - 1)))) (Abs NoId p)]-}
      fun hid = (2,
                 do p1 <- newPlaceholder
                    p2 <- newPlaceholder
                    return $ Fun hid p1 p2)
      pi hid = (2,
                do p1 <- newPlaceholder
                   p2 <- newPlaceholder
                   return $ Pi hid p1 (Abs NoId p2))
      mimic = case unis of
               [] -> []
               (RIUnifInfo _ cl hnopp : _) -> case hnopp of
                HNApp (Const c) _ -> [capp c]
                _ -> []
               _ -> error "refinements: mimic: not matched"
  case tt of
   HNFun hid _ _ -> return $ lam hid : apps ++ capps ++ mimic
   HNPi hid _ _ -> return $ lam hid : apps ++ capps ++ mimic
   HNSort (SortLevel l) -> return $ set l ++ [fun NotHidden, fun Hidden, pi NotHidden, pi Hidden] ++ apps ++ capps ++ mimic
   _ -> return $ apps ++ capps ++ mimic
 printref x = printExp [] (NotM x)

-- ---------------------------------

occursCheck :: forall a o . Metavar a (RefInfo o) -> HNExp o -> IO Bool
occursCheck m0 hn = liftM snd $ runStateT (
  let f :: forall b . Traversible b (RefInfo o) => MM b (RefInfo o) -> StateT Bool IO ()
      f (NotM x) = traverse f x
      f (Meta m) = do
         bind <- lift $ readIORef $ mbind m
         case bind of
          Just x -> traverse f x
          Nothing -> when (hequalMetavar m m0) $ put True
  in  traverse f hn
 ) False



{-
--
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

instance Refinable (Tagged (Exp o)) (RefInfo o) where
 refinements (RIEnv hints) infos =
  let (RIMainInfo n tt, unis) = getinfo infos Nothing []
      lam hid = do p <- newPlaceholder
               return $ Tagged (CMGuessed, error "no uid") $ Lam hid (Abs NoId p)
  in
   case unis of
    [] ->
     let
      apps = map app [0..n - 1]
      capps = map capp hints
      app v = do p <- newPlaceholder
                 -- h <- newOKHandle
                 return $ Tagged (CMGuessed, error "no uid") $ App (Var v) p
      capp c = do p <- newPlaceholder
                  -- h <- newOKHandle
                  return $ Tagged (CMGuessed, error "no uid") $ App (Const c) p
      set 0 = []
      -- set l = [return $ Sort (SortLevel (l - 1))]
      set l = [do p <- newPlaceholder
                  return $ Tagged (CMGuessed, error "no uid") $ Pi (NotM (Tagged (CMGuessed, error "no uid") $ Sort (SortLevel (l - 1)))) (Abs NoId p)]
      fun = do p1 <- newPlaceholder
               p2 <- newPlaceholder
               return $ Tagged (CMGuessed, error "no uid") $ Fun p1 p2
      pi = do p1 <- newPlaceholder
              p2 <- newPlaceholder
              return $ Tagged (CMGuessed, error "no uid") $ Pi p1 (Abs NoId p2)
     in
      case tt of
       HNFun hid _ _ -> lam hid : apps
       HNPi hid _ _ -> lam hid : apps
       HNSort (SortLevel l) -> fun : pi : set l ++ apps ++ capps
       _ -> apps ++ capps
    Right (RIUnifInfo cl oppe) ->
     let
      gapp v = do p <- newPlaceholder
                  -- h <- newOKHandle
                  return $ Tagged (CMGuessed, error "no uid") $ App (Var v) p
      app v = [do p <- newPlaceholder
                  uid <- getUId
                  -- h <- newOKHandle
                  return $ Tagged (CMCopied uid, uid) $ App (Var v) p]
      capp c = [do p <- newPlaceholder
                   uid <- getUId
                   -- h <- newOKHandle
                   return $ Tagged (CMCopied uid, uid) $ App (Const c) p]
      set l = [return $ Tagged (CMGuessed, error "no uid") $ Sort (SortLevel l)]
      fun = [do p1 <- newPlaceholder
                p2 <- newPlaceholder
                uid <- getUId
                return $ Tagged (CMCopied uid, uid) $ Fun p1 p2]
      pi = [do p1 <- newPlaceholder
               p2 <- newPlaceholder
               uid <- getUId
               return $ Tagged (CMCopied uid, uid) $ Pi p1 (Abs NoId p2)]
      copy =
       case oppe of
        HNApp (Var v) _ ->
         case univar cl v of
          Nothing -> []  -- var not in scope
          Just v' -> app v'
        HNApp (Const c) _ -> capp c
        HNLam _ -> []
        HNFun _ _ -> fun
        HNPi _ _ -> pi
        HNSort (SortLevel l) -> set l
        HNSort Type -> error "refinements.2: pattern not matched"
     in
      lam : map gapp (subsvars cl) ++ copy
    _ -> error "refinements: pattern not matched"
 printref x = printExp [] (NotM x)
--
-}

{-
instance Refinable Exp ExpBlkInfo where
 refinements infos =
  let (RIMainInfo n hints tt, munifi) = extrinfo infos
      apps = map app [0..n - 1]
      capps = map capp hints
      unis = case munifi of
              Nothing -> []
              Just (RIUnifInfo cl oppe) -> case oppe of
               HNApp (Const c) _ -> [capp c]
               _ -> []
      lam = do p <- newPlaceholder
               return $ Lam (Abs NoId p)
      app v = do p <- newPlaceholder
                 return $ App (Var v) p CMGuessed
      capp c = do p <- newPlaceholder
                  return $ App (Const c) p CMGuessed
      set 0 = []
      -- set l = [return $ Sort (SortLevel (l - 1))]
      set l = [do p <- newPlaceholder
                  return $ Pi (NotM (Sort (SortLevel (l - 1)))) (Abs NoId p) CMGuessed]
      fun = do p1 <- newPlaceholder
               p2 <- newPlaceholder
               return $ Fun p1 p2 CMGuessed
      pi = do p1 <- newPlaceholder
              p2 <- newPlaceholder
              return $ Pi p1 (Abs NoId p2) CMGuessed
  in
   case tt of
    HNFun _ _ -> lam : apps ++ unis
    HNPi _ _ -> lam : apps ++ unis
    HNSort (SortLevel l) -> fun : pi : set l ++ apps ++ capps ++ unis
    _ -> apps ++ capps ++ unis

extrinfo :: [ExpBlkInfo] -> (ExpBlkInfo, Maybe ExpBlkInfo)
extrinfo = loop Nothing Nothing
 where loop Nothing munifi (maini@(RIMainInfo _ _ _) : is) = loop (Just maini) munifi is
       loop (Just _) munifi (maini@(RIMainInfo _ _ _) : is) = error "extrinfo: already main info"
       loop mmaini _ (unifi@(RIUnifInfo _ _) : is) = loop mmaini (Just unifi) is  -- throwing away prev unif info (how to handle nicely?)
       loop (Just maini) munifi [] = (maini, munifi)
       loop Nothing _ [] = error "extrinfo: no main info"
-}

-- ---------------------------------

prioNo, prioTypeUnknown, prioTypecheckArgList, prioInferredTypeUnknown, prioPreCompare, prioCompare, prioCompareArgList, prioCompIota, prioCompChoice :: Int
-- cost version
{-
prioNo = 1000000  -- (-1)
prioTypeUnknown = 1000  -- 0
prioTypecheck False = 10  -- 1
prioTypecheck True = 1000  -- 0
prioTypecheckArgList = 2  -- 3
prioInferredTypeUnknown = 1000  -- 4
prioPreCompare = 1000  -- 4
prioCompChoice = 1
prioCompIota = 1000  -- 4
prioCompare = 5  -- 2
prioCompareArgList = 5  -- 2
-}

{-
prioNo = 1000000  -- (-1)
prioTypeUnknown = 1000  -- 0
prioTypecheck False = 10  -- 1
prioTypecheck True = 1000  -- 0
prioTypecheckArgList = 2  -- 3
prioInferredTypeUnknown = 1  -- 4
prioPreCompare = 1  -- 4
prioCompare = 5  -- 2
prioCompareArgList = 5  -- 2
prioCompIota = 1  -- 4
-}

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


{-
prioTypeUnknown = 0
prioTypecheck False = 2
prioTypecheck True = 1
prioTypecheckArgList = 4
prioInferredTypeUnknown = 5
prioPreCompare = 5
prioCompare = 3
prioCompareArgList = 3
-}

-- ---------------------------------

instance Traversible a blk => Traversible [a] blk where
 traverse _ [] = return ()
 traverse f (x:xs) = traverse f x >> traverse f xs

instance Traversible (MId, CExp o) (RefInfo o) where
 traverse f (_, ce) = traverse f ce

instance Traversible a (RefInfo o) => Traversible (Clos a o) (RefInfo o) where
 traverse f (Clos cl e) = traverse f cl >> traverse f e

instance Traversible (CAction o) (RefInfo o) where
 traverse f (Sub ce) = traverse f ce
 traverse _ Skip = return ()
 traverse _ (Weak _) = return ()

instance Traversible (Exp o) (RefInfo o) where
 traverse f e = case e of
  App _ args -> traverse f args
  Lam _ (Abs _ b) -> traverse f b
  Fun _ it ot -> traverse f it >> traverse f ot
  Pi _ it (Abs _ ot) -> traverse f it >> traverse f ot
  Sort _ -> return ()

instance Traversible (ArgList o) (RefInfo o) where
 traverse _ ALNil = return ()
 traverse f (ALCons _ arg args) = traverse f arg >> traverse f args
 traverse f (ALConPar args) = traverse f args

instance Traversible (HNExp o) (RefInfo o) where
 traverse f e = case e of
  HNApp _ args -> traverse f args
  HNLam (Abs _ b) -> traverse f b
  HNFun _ it ot -> traverse f it >> traverse f ot
  HNPi _ it (Abs _ ot) -> traverse f it >> traverse f ot
  HNSort _ -> return ()

instance Traversible (CArgList o) (RefInfo o) where
 traverse _ CALNil = return ()
 traverse f (CALConcat arg args) = traverse f arg >> traverse f args

