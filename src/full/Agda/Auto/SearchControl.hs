{-# LANGUAGE UndecidableInstances, MultiParamTypeClasses,
             TypeSynonymInstances, FlexibleInstances, CPP #-}

module Agda.Auto.SearchControl where

import Agda.Utils.Impossible
#include "../undefined.h"

import Control.Monad
import Data.IORef
import Control.Monad.State
import Data.Maybe (mapMaybe)

import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax


instance Refinable (ArgList o) (RefInfo o) where
 refinements _ infos _ =
  return $ [
            (0, return ALNil),

            (0, cons NotHidden),
            (0, cons Hidden)


           ]

           ++
           (let isdep = rr infos
                rr (RICheckElim isdep : _) = isdep
                rr (_ : xs) = rr xs
                rr _ = __IMPOSSIBLE__
                proj hid = newPlaceholder >>= \p1 -> newPlaceholder >>= \p2 -> newPlaceholder >>= \p3 -> return $ ALProj p1 p2 hid p3
            in if isdep then
                 []
                else

                 [(0, proj NotHidden), (0, proj Hidden)]


           )

  where cons hid = newPlaceholder >>= \p1 -> newPlaceholder >>= \p2 -> return $ ALCons hid p1 p2


data ExpRefInfo o = ExpRefInfo {eriMain :: Maybe (RefInfo o), eriUnifs :: [RefInfo o], eriInfTypeUnknown, eriIsEliminand :: Bool, eriUsedVars :: Maybe ([UId o], [Elr o]),
                                eriIotaStep :: Maybe Bool, eriPickSubsVar :: Bool

                                , eriEqRState :: Maybe EqReasoningState

                               }

getinfo = f (ExpRefInfo {eriMain = Nothing, eriUnifs = [], eriInfTypeUnknown = False, eriIsEliminand = False, eriUsedVars = Nothing,
                         eriIotaStep = Nothing, eriPickSubsVar = False

                         , eriEqRState = Nothing

                        })
 where
  f i [] = i
  f i (x@RIMainInfo{} : xs) = f (i {eriMain = Just x}) xs
  f i (x@RIUnifInfo{} : xs) = f (i {eriUnifs = x : eriUnifs i}) xs
  f i (RIInferredTypeUnknown : xs) = f (i {eriInfTypeUnknown = True}) xs
  f i (RINotConstructor : xs) = f (i {eriIsEliminand = True}) xs
  f i (RIUsedVars nuids nused : xs) = f (i {eriUsedVars = Just (nuids, nused)}) xs
  f i (RIIotaStep semif : xs) = f (i {eriIotaStep = Just (semif || maybe False id (eriIotaStep i))}) xs
  f i (RIPickSubsvar : xs) = f (i {eriPickSubsVar = True}) xs

  f i (RIEqRState s : xs) = f (i {eriEqRState = Just s}) xs

  f i _ = __IMPOSSIBLE__


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
   hints = rieHints envinfo
   deffreevars = rieDefFreeVars envinfo

   meqr = rieEqReasoningConsts envinfo

   ExpRefInfo {eriMain = Just (RIMainInfo n tt iotastepdone), eriUnifs = unis, eriInfTypeUnknown = inftypeunknown, eriIsEliminand = iseliminand, eriUsedVars = Just (uids, usedvars),
                         eriIotaStep = iotastep, eriPickSubsVar = picksubsvar

                         , eriEqRState = meqrstate

                        } = getinfo infos

   eqrstate = maybe EqRSNone id meqrstate

   app muid elr = do p <- newPlaceholder
                     p <- case elr of
                      Var{} -> return p
                      Const c -> do
                       cd <- lift $ readIORef c
                       let dfvapp 0 _ = p
                           dfvapp i n = NotM $ ALCons NotHidden (NotM $ App Nothing (NotM $ OKVal) (Var n) (NotM ALNil)) (dfvapp (i - 1) (n - 1))
                            -- NotHidden is ok because agda reification throws these arguments away and agsy skips typechecking them
                       return $ dfvapp (cddeffreevars cd) (n - 1)

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

     eqr = maybe __IMPOSSIBLE__ id meqr
     foldargs [] = NotM ALNil
     foldargs ((h, a) : xs) = NotM $ ALCons h a (foldargs xs)
     eq_begin_step_step = (costEqStep,
                       do psb <- replicateM 4 newPlaceholder
                          okhb <- newOKHandle
                          pss1 <- replicateM 6 newPlaceholder
                          okhs1 <- newOKHandle
                          pss2 <- replicateM 7 newPlaceholder
                          okhs2 <- newOKHandle
                          return $ App (Just meta) okhb (Const $ eqrcBegin eqr) (foldargs (zip [Hidden, Hidden, Hidden, Hidden, NotHidden] (psb ++ [
                            NotM $ App (Just meta) okhs1 (Const $ eqrcStep eqr) (foldargs (zip [Hidden, Hidden, NotHidden, Hidden, Hidden, NotHidden, NotHidden] (pss1 ++ [
                             NotM $ App (Just meta) okhs2 (Const $ eqrcStep eqr) (foldargs (zip [Hidden, Hidden, NotHidden, Hidden, Hidden, NotHidden, NotHidden] pss2))
                            ])))
                           ])))
                      )
     eq_step = (costEqStep,
                 do ps <- replicateM 7 newPlaceholder
                    okh <- newOKHandle
                    return $ App (Just meta) okh (Const $ eqrcStep eqr) (foldargs (zip [Hidden, Hidden, NotHidden, Hidden, Hidden, NotHidden, NotHidden] ps))
                )
     eq_end = (costEqEnd,
               do ps <- replicateM 3 newPlaceholder
                  okh <- newOKHandle
                  return $ App (Just meta) okh (Const $ eqrcEnd eqr) (foldargs (zip [Hidden, Hidden, NotHidden] ps))
              )
     eq_sym = (costEqSym,
               do ps <- replicateM 5 newPlaceholder
                  okh <- newOKHandle
                  return $ App (Just meta) okh (Const $ eqrcSym eqr) (foldargs (zip [Hidden, Hidden, Hidden, Hidden, NotHidden] ps))
              )
     eq_cong = (costEqCong,
                do ps <- replicateM 8 newPlaceholder
                   okh <- newOKHandle
                   return $ App (Just meta) okh (Const $ eqrcCong eqr) (foldargs (zip [Hidden, Hidden, Hidden, Hidden, NotHidden, Hidden, Hidden, NotHidden] ps))
               )

     pcav i = if inftypeunknown then costInferredTypeUnkown else i
     pc i = pcav i
     varcost v | v < n - deffreevars = pcav (case Just usedvars of {Just usedvars -> if elem v (mapMaybe (\x -> case x of {Var v -> Just v; Const{} -> Nothing}) usedvars) then costAppVarUsed else costAppVar; Nothing -> if picksubsvar then costAppVar else costAppVarUsed})
     varcost v | otherwise = pcav costAppHint
     varapps = map (\v ->
                (varcost v,
                 app Nothing (Var v)
                )) [0..n - 1]
     hintapps = map (\(c, hm) ->
                 (cost c hm,
                  app Nothing (Const c)
                 )) hints
                 where cost c hm = pc (case iotastep of
                                        Just _ -> costIotaStep
                                        Nothing -> if elem c (mapMaybe (\x -> case x of {Var{} -> Nothing; Const c -> Just c}) usedvars) then
                                          case hm of {HMNormal -> costAppHintUsed; HMRecCall -> costAppRecCallUsed}
                                         else
                                          case hm of {HMNormal -> costAppHint; HMRecCall -> costAppRecCall})
     generics = varapps ++ hintapps
    in case tt of

     _ | eqrstate == EqRSChain ->
      return $ [eq_end, eq_step]

     HNPi _ hid possdep _ (Abs id _) -> return $ (pc (if iotastepdone then costLamUnfold else costLam), lam hid id) : (costAbsurdLam, return $ AbsurdLambda hid) : generics

     HNSort (Set l) -> return $ map (\l -> (pc costSort, set l)) [0..l - 1] ++ [(pc costPi, pi Nothing True NotHidden), (pc costPi, pi Nothing True Hidden)] ++ generics


     HNApp _ (Const c) _ -> do
      cd <- readIORef c
      return $ case cdcont cd of
       Datatype cons _

        | eqrstate == EqRSNone

         -> map (\c -> (pc (case iotastep of {Just True -> costUnification; _ -> if length cons <= 1 then costAppConstructorSingle else costAppConstructor}), app Nothing (Const c))) cons ++
            generics

            ++ if maybe False (\eqr -> c == eqrcId eqr) meqr then [eq_sym, eq_cong, eq_begin_step_step] else []
       _ | eqrstate == EqRSPrf1 -> generics ++ [eq_sym, eq_cong]
       _ | eqrstate == EqRSPrf2 -> generics ++ [eq_cong]

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

     pickuid seenuids =
      case f seenuids of
       Just uid -> (uid, True)
       Nothing -> (head seenuids, False) -- ?? which uid to pick
      where f [] = Nothing
            f (Nothing:_) = Just Nothing
            f (Just u:us) = if elem u uids then f us else Just (Just u)
    in
     return $ case hne of
      HNApp seenuids (Var v) _ ->
       let (uid, isunique) = pickuid seenuids
           uni = case univar cl v of
                  Just v | v < n -> [(if isunique then costUnification else costUnificationOccurs, app uid (Var v))]
                  _ -> []
       in uni ++ generics
      HNApp seenuids (Const c) _ ->
       let (uid, isunique) = pickuid seenuids
       in (if isunique then costUnification else costUnificationOccurs, app uid (Const c)) : generics
      HNLam{} -> generics
      HNPi seenuids hid possdep _ _ ->
       let (uid, isunique) = pickuid seenuids
       in (if isunique then costUnification else costUnificationOccurs, pi uid possdep hid) : generics
      HNSort (Set l) -> map (\l -> (costUnification, set l)) [0..l] ++ generics
      HNSort _ -> generics
   _ -> __IMPOSSIBLE__


extraref meta seenuids c = (costAppExtraRef, app (head seenuids) (Const c))
 where
   app muid elr = do p <- newPlaceholder
                     okh <- newOKHandle
                     let uid = case muid of
                                Just _ -> muid
                                Nothing -> Just meta
                     return $ App uid okh elr p


instance Refinable (ICExp o) (RefInfo o) where
 refinements _ infos _ =
  let (RICopyInfo e : _) = infos
  in return [(0, return e)]


instance Refinable (ConstRef o) (RefInfo o) where
 refinements _ [RICheckProjIndex projs] _ = return $ map (\x -> (0, return x)) projs
 refinements _ _ _ = __IMPOSSIBLE__


-- ---------------------------------
costIotaStep, costAppExtraRef, costIncrease :: Int
costIncrease = 1000
costUnificationOccurs = 100 -- 1000001 -- 1 -- 100
costUnification = 0000
costAppVar = 0000 -- 0, 1
costAppVarUsed = 1000 -- 5
costAppHint = 3000 -- 2, 5
costAppHintUsed = 5000
costAppRecCall = 0 -- 1000?
costAppRecCallUsed = 10000 -- 1000?
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

costEqStep = 2000
costEqEnd = 0
costEqSym = 0
costEqCong = 500


prioNo, prioTypeUnknown, prioTypecheckArgList, prioInferredTypeUnknown, prioCompBeta, prioCompBetaStructured, prioCompareArgList, prioCompIota, prioCompChoice, prioCompUnif, prioCompCopy, prioNoIota, prioAbsurdLambda :: Int
prioNo = (-1)
prioTypeUnknown = 0
prioTypecheck False = 1000
prioTypecheck True = 0
prioTypecheckArgList = 3000
prioInferredTypeUnknown = 4000
prioCompBeta = 4000
prioCompBetaStructured = 4000
prioCompIota = 4000
prioCompChoice = 5000 -- 700 -- 5000
prioCompUnif = 6000 -- 2
prioCompCopy = 8000
prioCompareArgList = 7000 -- 5 -- 2
prioNoIota = 500 -- 500
prioAbsurdLambda = 1000

prioProjIndex = 3000 :: Int


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

 traverse f (ALProj eas _ _ as) = traverse f eas >> traverse f as


 traverse f (ALConPar args) = traverse f args


-- ---------------------------------
