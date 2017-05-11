{-# LANGUAGE CPP                   #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Auto.SearchControl where

import Control.Applicative hiding (getConst, Const(..))
import Control.Monad
import Data.IORef
import Control.Monad.State
import Data.Maybe (mapMaybe, fromMaybe)

import Agda.Syntax.Common (Hiding(..))
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax

#include "undefined.h"
import Agda.Utils.Impossible

instance Refinable (ArgList o) (RefInfo o) where
 refinements _ infos _ = return $ fmap (0,) $
   [ return ALNil, cons NotHidden, cons Hidden ]
   ++ if getIsDep infos then []
      else [ proj NotHidden, proj Hidden ]

   where

    getIsDep :: [RefInfo o] -> Bool
    getIsDep (x : xs) = case x of
      RICheckElim isDep -> isDep
      _                 -> getIsDep xs
    getIsDep _ = __IMPOSSIBLE__

    proj :: Hiding -> RefCreateEnv (RefInfo o) (ArgList o)
    proj hid = ALProj <$> newPlaceholder <*> newPlaceholder
                      <*> return hid     <*> newPlaceholder

    cons :: Hiding -> RefCreateEnv (RefInfo o) (ArgList o)
    cons hid = ALCons hid <$> newPlaceholder <*> newPlaceholder


data ExpRefInfo o = ExpRefInfo
  { eriMain           :: Maybe (RefInfo o)
  , eriUnifs          :: [RefInfo o]
  , eriInfTypeUnknown :: Bool
  , eriIsEliminand    :: Bool
  , eriUsedVars       :: Maybe ([UId o], [Elr o])
  , eriIotaStep       :: Maybe Bool
  , eriPickSubsVar    :: Bool
  , eriEqRState       :: Maybe EqReasoningState
  }

initExpRefInfo :: ExpRefInfo o
initExpRefInfo = ExpRefInfo
  { eriMain           = Nothing
  , eriUnifs          = []
  , eriInfTypeUnknown = False
  , eriIsEliminand    = False
  , eriUsedVars       = Nothing
  , eriIotaStep       = Nothing
  , eriPickSubsVar    = False
  , eriEqRState       = Nothing
  }

getinfo :: [RefInfo o] -> ExpRefInfo o
getinfo = foldl step initExpRefInfo where

  step :: ExpRefInfo o -> RefInfo o -> ExpRefInfo o
  step eri x@RIMainInfo{}           = eri { eriMain  = Just x }
  step eri x@RIUnifInfo{}           = eri { eriUnifs = x : eriUnifs eri }
  step eri RIInferredTypeUnknown    = eri { eriInfTypeUnknown = True }
  step eri RINotConstructor         = eri { eriIsEliminand = True }
  step eri (RIUsedVars nuids nused) = eri { eriUsedVars = Just (nuids, nused) }
  step eri (RIIotaStep semif)       = eri { eriIotaStep = Just iota' } where
    iota' = semif || fromMaybe False (eriIotaStep eri)
  step eri RIPickSubsvar            = eri { eriPickSubsVar = True }
  step eri (RIEqRState s)           = eri { eriEqRState = Just s }
  step eri _ = __IMPOSSIBLE__


univar :: [CAction o] -> Nat -> Maybe Nat
univar cl v = f cl v 0 where

  f :: [CAction o] -> Nat -> Nat -> Maybe Nat
  f []            v v' = Just (v' + v)
  f (Weak n : _)  v v' | v < n = Nothing
  f (Weak n : xs) v v' = f xs (v - n) v'
  f (Sub _  : xs) v v' = f xs v (v' + 1)
  f (Skip   : _)  0 v' = Just v'
  f (Skip   : xs) v v' = f xs (v - 1) (v' + 1)

-- | List of the variables instantiated by the substitution
subsvars :: [CAction o] -> [Nat]
subsvars = f 0 where

  f :: Nat -> [CAction o] -> [Nat]
  f n []            = []
  f n (Weak _ : xs) = f n xs -- why?
  f n (Sub _  : xs) = n : f (n + 1) xs
  f n (Skip   : xs) = f (n + 1) xs

newAbs :: MId -> RefCreateEnv blk (Abs (MM a blk))
newAbs mid = Abs mid <$> newPlaceholder

newLam :: Hiding -> MId -> RefCreateEnv (RefInfo o) (Exp o)
newLam hid mid = Lam hid <$> newAbs mid

newPi :: UId o -> Bool -> Hiding -> RefCreateEnv (RefInfo o) (Exp o)
newPi uid dep hid = Pi (Just uid) hid dep <$> newPlaceholder <*> newAbs NoId

instance Refinable (Exp o) (RefInfo o) where
 refinements envinfo infos meta =
  let
   hints = rieHints envinfo
   deffreevars = rieDefFreeVars envinfo

   meqr = rieEqReasoningConsts envinfo

   ExpRefInfo { eriMain  = Just (RIMainInfo n tt iotastepdone)
              , eriUnifs = unis
              , eriInfTypeUnknown = inftypeunknown
              , eriIsEliminand = iseliminand
              , eriUsedVars = Just (uids, usedvars)
              , eriIotaStep = iotastep
              , eriPickSubsVar = picksubsvar
              , eriEqRState = meqrstate
              } = getinfo infos

   eqrstate = fromMaybe EqRSNone meqrstate

   app muid elr = do
     p <- newPlaceholder
     p <- case elr of
            Var{}   -> return p
            Const c -> do
              cd <- RefCreateEnv $ lift $ readIORef c
              let dfvapp 0 _ = p
                  dfvapp i n = NotM $ ALCons NotHidden
                                      (NotM $ App Nothing (NotM $ OKVal) (Var n) (NotM ALNil))
                                      (dfvapp (i - 1) (n - 1))
                  -- NotHidden is ok because agda reification throws these arguments away and agsy skips typechecking them
              return $ dfvapp (cddeffreevars cd) (n - 1)
     okh <- newOKHandle
     return $ App (Just $ fromMaybe meta muid) okh elr p
   set l = return $ Sort (Set l)
  in case unis of
   [] ->
    let

     eqr = fromMaybe __IMPOSSIBLE__ meqr
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

     HNPi _ hid possdep _ (Abs id _) -> return $ (pc (if iotastepdone then costLamUnfold else costLam), newLam hid id) : (costAbsurdLam, return $ AbsurdLambda hid) : generics

     HNSort (Set l) -> return $ map (\l -> (pc costSort, set l)) [0..l - 1]
                          ++ [(pc costPi, newPi meta True NotHidden), (pc costPi, newPi meta True Hidden)] ++ generics


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
      HNPi _ hid _ _ (Abs id _) -> [(costUnification, newLam hid id)]
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
       in (if isunique then costUnification else costUnificationOccurs
          , newPi (fromMaybe meta uid) possdep hid) : generics
      HNSort (Set l) -> map (\l -> (costUnification, set l)) [0..l] ++ generics
      HNSort _ -> generics
   _ -> __IMPOSSIBLE__

extraref :: UId o -> [Maybe (UId o)] -> ConstRef o ->
            (Int, RefCreateEnv (RefInfo o) (Exp o))
extraref meta seenuids c = (costAppExtraRef, app (head seenuids) (Const c))
 where
   app muid elr = App (Just $ fromMaybe meta muid)
              <$> newOKHandle <*> return elr <*> newPlaceholder

instance Refinable (ICExp o) (RefInfo o) where
 refinements _ infos _ =
  let (RICopyInfo e : _) = infos
  in return [(0, return e)]


instance Refinable (ConstRef o) (RefInfo o) where
 refinements _ [RICheckProjIndex projs] _ = return $ map (\x -> (0, return x)) projs
 refinements _ _ _ = __IMPOSSIBLE__


-- ---------------------------------

costIncrease, costUnificationOccurs, costUnification, costAppVar,
  costAppVarUsed, costAppHint, costAppHintUsed, costAppRecCall,
  costAppRecCallUsed, costAppConstructor, costAppConstructorSingle,
  costAppExtraRef, costLam, costLamUnfold, costPi, costSort, costIotaStep,
  costInferredTypeUnkown, costAbsurdLam
  :: Int

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

costEqStep, costEqEnd, costEqSym, costEqCong :: Int
costEqStep = 2000
costEqEnd = 0
costEqSym = 0
costEqCong = 500

prioNo, prioTypeUnknown, prioTypecheckArgList, prioInferredTypeUnknown,
  prioCompBeta, prioCompBetaStructured, prioCompareArgList, prioCompIota,
  prioCompChoice, prioCompUnif, prioCompCopy, prioNoIota, prioAbsurdLambda,
  prioProjIndex
  :: Int
prioNo = (-1)
prioTypeUnknown = 0
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

prioProjIndex = 3000

prioTypecheck :: Bool -> Int
prioTypecheck False = 1000
prioTypecheck True = 0

-- ---------------------------------

instance Trav a blk => Trav [a] blk where
  trav _ []     = return ()
  trav f (x:xs) = trav f x >> trav f xs

instance Trav (MId, CExp o) (RefInfo o) where
  trav f (_, ce) = trav f ce

instance Trav (TrBr a o) (RefInfo o) where
  trav f (TrBr es _) = trav f es

instance Trav (Exp o) (RefInfo o) where
  trav f e = case e of
    App _ _ _ args          -> trav f args
    Lam _ (Abs _ b)        -> trav f b
    Pi _ _ _ it (Abs _ ot) -> trav f it >> trav f ot
    Sort _                 -> return ()
    AbsurdLambda{}         -> return ()

instance Trav (ArgList o) (RefInfo o) where
  trav _ ALNil               = return ()
  trav f (ALCons _ arg args) = trav f arg >> trav f args
  trav f (ALProj eas _ _ as) = trav f eas >> trav f as
  trav f (ALConPar args)     = trav f args

-- ---------------------------------
