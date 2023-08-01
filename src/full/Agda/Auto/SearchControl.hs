{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-orphans #-}
#if __GLASGOW_HASKELL__ > 907
{-# OPTIONS_GHC -Wno-x-partial #-}
#endif



module Agda.Auto.SearchControl where

import Control.Monad
import Data.IORef
import Control.Monad.State
import Data.Maybe (mapMaybe, fromMaybe)

import Agda.Syntax.Common (Hiding(..))
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax

import Agda.Utils.Impossible

instance Refinable (ArgList o) (RefInfo o) where
 refinements _ infos _ = return $ fmap (Move 0) $
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
    iota' = semif || (Just True ==) (eriIotaStep eri)
  step eri RIPickSubsvar            = eri { eriPickSubsVar = True }
  step eri (RIEqRState s)           = eri { eriEqRState = Just s }
  step eri _ = __IMPOSSIBLE__


-- | @univar sub v@ figures out what the name of @v@ "outside" of
--   the substitution @sub@ ought to be, if anything.

univar :: [CAction o] -> Nat -> Maybe Nat
univar cl v = getOutsideName cl v 0 where

  getOutsideName :: [CAction o] -> Nat -> Nat -> Maybe Nat
  -- @v@ is offset by @v'@ binders
  getOutsideName []            v v' = Just (v' + v)
  -- @v@ was introduced by the weakening: disappears
  getOutsideName (Weak n : _)  v v' | v < n = Nothing
  -- @v@ was introduced before the weakening: strengthened
  getOutsideName (Weak n : xs) v v' = getOutsideName xs (v - n) v'
  -- Name of @v@ before the substitution was pushed in
  -- had to be offset by 1
  getOutsideName (Sub _  : xs) v v' = getOutsideName xs v (v' + 1)
  -- If this is the place where @v@ was bound, it used to
  -- be called 0 + offset of all the vars substituted for
  getOutsideName (Skip   : _)  0 v' = Just v'
  -- Going over a binder: de Bruijn name of @v@ decreased
  -- but offset increased
  getOutsideName (Skip   : xs) v v' = getOutsideName xs (v - 1) (v' + 1)

-- | List of the variables instantiated by the substitution
subsvars :: [CAction o] -> [Nat]
subsvars = f 0 where

  f :: Nat -> [CAction o] -> [Nat]
  f n []            = []
  f n (Weak _ : xs) = f n xs -- why?
  f n (Sub _  : xs) = n : f (n + 1) xs
  f n (Skip   : xs) = f (n + 1) xs

-- | Moves
--   A move is composed of a @Cost@ together with an action
--   computing the refined problem.

type Move o = Move' (RefInfo o) (Exp o)

-- | New constructors
--   Taking a step towards a solution consists in picking a
--   constructor and filling in the missing parts with
--   placeholders to be discharged later on.

newAbs :: MId -> RefCreateEnv blk (Abs (MM a blk))
newAbs mid = Abs mid <$> newPlaceholder

newLam :: Hiding -> MId -> RefCreateEnv (RefInfo o) (Exp o)
newLam hid mid = Lam hid <$> newAbs mid

newPi :: UId o -> Bool -> Hiding -> RefCreateEnv (RefInfo o) (Exp o)
newPi uid dep hid = Pi (Just uid) hid dep <$> newPlaceholder <*> newAbs NoId

foldArgs :: [(Hiding, MExp o)] -> MArgList o
foldArgs = foldr (\ (h, a) sp -> NotM $ ALCons h a sp) (NotM ALNil)

-- | New spine of arguments potentially using placeholders

newArgs' :: [Hiding] -> [MExp o] -> RefCreateEnv (RefInfo o) (MArgList o)
newArgs' h tms = foldArgs . zip h . (++ tms) <$> replicateM size newPlaceholder
  where size = length h - length tms

newArgs :: [Hiding] -> RefCreateEnv (RefInfo o) (MArgList o)
newArgs h = newArgs' h []

-- | New @App@lication node using a new spine of arguments
--   respecting the @Hiding@ annotation

newApp' :: UId o -> ConstRef o -> [Hiding] -> [MExp o] ->
           RefCreateEnv (RefInfo o) (Exp o)
newApp' meta cst hds tms =
  App (Just meta) <$> newOKHandle <*> return (Const cst) <*> newArgs' hds tms

newApp :: UId o -> ConstRef o -> [Hiding] -> RefCreateEnv (RefInfo o) (Exp o)
newApp meta cst hds = newApp' meta cst hds []

-- | Equality reasoning steps
--   The begin token is accompanied by two steps because
--   it does not make sense to have a derivation any shorter
--   than that.

eqStep :: UId o -> EqReasoningConsts o -> Move o
eqStep meta eqrc = Move costEqStep $ newApp meta (eqrcStep eqrc)
  [Hidden, Hidden, NotHidden, Hidden, Hidden, NotHidden, NotHidden]

eqEnd :: UId o -> EqReasoningConsts o -> Move o
eqEnd meta eqrc = Move costEqEnd $ newApp meta (eqrcEnd eqrc)
  [Hidden, Hidden, NotHidden]

eqCong :: UId o -> EqReasoningConsts o -> Move o
eqCong meta eqrc = Move costEqCong $ newApp meta (eqrcCong eqrc)
  [Hidden, Hidden, Hidden, Hidden, NotHidden, Hidden, Hidden, NotHidden]

eqSym :: UId o -> EqReasoningConsts o -> Move o
eqSym meta eqrc = Move costEqSym $ newApp meta (eqrcSym eqrc)
  [Hidden, Hidden, Hidden, Hidden, NotHidden]

eqBeginStep2 :: UId o -> EqReasoningConsts o -> Move o
eqBeginStep2 meta eqrc = Move costEqStep $ do
  e1 <- newApp meta (eqrcStep eqrc)
          [Hidden, Hidden, NotHidden, Hidden, Hidden, NotHidden, NotHidden]
  e2 <- newApp' meta (eqrcStep eqrc)
          [Hidden, Hidden, NotHidden, Hidden, Hidden, NotHidden, NotHidden]
          [NotM e1]
  newApp' meta (eqrcBegin eqrc) [Hidden, Hidden, Hidden, Hidden, NotHidden]
    [NotM e2]


-- | Pick the first unused UId amongst the ones you have seen (GA: ??)
--   Defaults to the head of the seen ones.

pickUid :: forall o. [UId o] -> [Maybe (UId o)] -> (Maybe (UId o), Bool)
pickUid used seen = maybe (head seen, False) (, True) $ firstUnused seen where
  {- ?? which uid to pick -}

  firstUnused :: [Maybe (UId o)] -> Maybe (Maybe (UId o))
  firstUnused []                 = Nothing
  firstUnused (Nothing     : _)  = Just Nothing
  firstUnused (mu@(Just u) : us) =
    if u `elem` used then firstUnused us else Just mu

instance Refinable (Exp o) (RefInfo o) where
 refinements envinfo infos meta =
  let
   hints = rieHints envinfo
   deffreevars = rieDefFreeVars envinfo

   meqr = rieEqReasoningConsts envinfo

   ExpRefInfo { eriMain  = Just (RIMainInfo n tt iotastepdone)
              , eriUnifs = unis
              , eriInfTypeUnknown = inftypeunknown
              , eriIsEliminand = iseliminand -- TODO:: Defined but not used
              , eriUsedVars = Just (uids, usedvars)
              , eriIotaStep = iotastep
              , eriPickSubsVar = picksubsvar -- TODO:: Defined but not used
              , eriEqRState = meqrstate
              } = getinfo infos

   eqrstate = fromMaybe EqRSNone meqrstate

   set l = return $ Sort (Set l)
  in case unis of
   [] ->
    let

     eqr = fromMaybe __IMPOSSIBLE__ meqr
     eq_end         = eqEnd  meta eqr
     eq_step        = eqStep meta eqr
     eq_cong        = eqCong meta eqr
     eq_sym         = eqSym  meta eqr
     eq_begin_step2 = eqBeginStep2 meta eqr

     adjustCost i = if inftypeunknown then costInferredTypeUnkown else i
     varcost v | v < n - deffreevars = adjustCost $
       if v `elem` (mapMaybe getVar usedvars)
       then costAppVarUsed else costAppVar
     varcost v | otherwise           = adjustCost costAppHint
     varapps  = map (\ v -> Move (varcost v) $ app n meta Nothing (Var v)) [0..n - 1]
     hintapps = map (\(c, hm) -> Move (cost c hm) (app n meta Nothing (Const c))) hints
       where
         cost :: ConstRef o -> HintMode -> Cost
         cost c hm = adjustCost $ case (iotastep , hm) of
           (Just _  , _       ) -> costIotaStep
           (Nothing , HMNormal) ->
             if c `elem` (mapMaybe getConst usedvars)
             then costAppHintUsed else costAppHint
           (Nothing , HMRecCall) ->
             if c `elem` (mapMaybe getConst usedvars)
             then costAppRecCallUsed else costAppRecCall
     generics = varapps ++ hintapps
    in case rawValue tt of

     _ | eqrstate == EqRSChain ->
      return [eq_end, eq_step]

     HNPi hid _ _ (Abs id _) -> return $
         Move (adjustCost (if iotastepdone then costLamUnfold else costLam)) (newLam hid id)
       : Move costAbsurdLam (return $ AbsurdLambda hid)
       : generics

     HNSort (Set l) -> return $
          map (Move (adjustCost costSort) . set) [0..l - 1]
       ++ map (Move (adjustCost costPi) . newPi meta True) [NotHidden, Hidden]
       ++ generics


     HNApp (Const c) _ -> do
      cd <- readIORef c
      return $ case cdcont cd of

       Datatype cons _ | eqrstate == EqRSNone ->
         map (\c -> Move (adjustCost $ case iotastep of
                                         Just True -> costUnification
                                         _ -> if length cons <= 1
                                              then costAppConstructorSingle
                                              else costAppConstructor)
                         $ app n meta Nothing (Const c)) cons
         ++ generics
         ++ (guard (maybe False ((c ==) . eqrcId) meqr)
            *> [eq_sym, eq_cong, eq_begin_step2])

       _ | eqrstate == EqRSPrf1 -> generics ++ [eq_sym, eq_cong]
       _ | eqrstate == EqRSPrf2 -> generics ++ [eq_cong]

       _ -> generics
     _ -> return generics
   (RIUnifInfo cl hne : _) ->
    let
     subsvarapps = map (Move costUnification . app n meta Nothing . Var) (subsvars cl)
     mlam = case rawValue tt of
      HNPi hid _ _ (Abs id _) -> [Move costUnification (newLam hid id)]
      _ -> []
     generics = mlam ++ subsvarapps

    in
     return $ case rawValue hne of
      HNApp (Var v) _ ->
       let (uid, isunique) = pickUid uids $ seenUIds hne
           uni = case univar cl v of
                  Just v | v < n -> [Move (costUnificationIf isunique) $ app n meta uid (Var v)]
                  _ -> []
       in uni ++ generics
      HNApp (Const c) _ ->
       let (uid, isunique) = pickUid uids $ seenUIds hne
       in Move (costUnificationIf isunique) (app n meta uid (Const c)) : generics
      HNLam{} -> generics
      HNPi hid possdep _ _ ->
       let (uid, isunique) = pickUid uids $ seenUIds hne
       in Move (costUnificationIf isunique) (newPi (fromMaybe meta uid) possdep hid) : generics
      HNSort (Set l) -> map (Move costUnification . set) [0..l] ++ generics
      HNSort _ -> generics
   _ -> __IMPOSSIBLE__

  where

    app :: Nat -> UId o -> Maybe (UId o) -> Elr o ->
           RefCreateEnv (RefInfo o) (Exp o)
    app n meta muid elr = do
      p <- newPlaceholder
      p <- case elr of
        Var{}   -> return p
        Const c -> do
          cd <- RefCreateEnv $ lift $ readIORef c
          let dfvapp 0 _ = p
              dfvapp i n = NotM $ ALCons NotHidden
                          (NotM $ App Nothing (NotM $ OKVal) (Var n) (NotM ALNil))
                          (dfvapp (i - 1) (n - 1))
         -- NotHidden is ok because agda reification throws these arguments
         -- away and agsy skips typechecking them
          return $ dfvapp (cddeffreevars cd) (n - 1)
      okh <- newOKHandle
      return $ App (Just $ fromMaybe meta muid) okh elr p


extraref :: UId o -> [Maybe (UId o)] -> ConstRef o -> Move o
extraref meta seenuids c = Move costAppExtraRef $ app (head seenuids) (Const c)
 where
   app muid elr = App (Just $ fromMaybe meta muid)
              <$> newOKHandle <*> return elr <*> newPlaceholder

instance Refinable (ICExp o) (RefInfo o) where
 refinements _ infos _ =
  let (RICopyInfo e : _) = infos
  in return [Move 0 (return e)]


instance Refinable (ConstRef o) (RefInfo o) where
 refinements _ [RICheckProjIndex projs] _ = return $ map (Move 0 . return) projs
 refinements _ _ _ = __IMPOSSIBLE__


-- ---------------------------------

costIncrease, costUnificationOccurs, costUnification, costAppVar,
  costAppVarUsed, costAppHint, costAppHintUsed, costAppRecCall,
  costAppRecCallUsed, costAppConstructor, costAppConstructorSingle,
  costAppExtraRef, costLam, costLamUnfold, costPi, costSort, costIotaStep,
  costInferredTypeUnkown, costAbsurdLam
  :: Cost

costUnificationIf :: Bool -> Cost
costUnificationIf b = if b then costUnification else costUnificationOccurs

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

costEqStep, costEqEnd, costEqSym, costEqCong :: Cost
costEqStep = 2000
costEqEnd = 0
costEqSym = 0
costEqCong = 500

prioNo, prioTypeUnknown, prioTypecheckArgList, prioInferredTypeUnknown,
  prioCompBeta, prioCompBetaStructured, prioCompareArgList, prioCompIota,
  prioCompChoice, prioCompUnif, prioCompCopy, prioNoIota, prioAbsurdLambda,
  prioProjIndex
  :: Prio
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

prioTypecheck :: Bool -> Prio
prioTypecheck False = 1000
prioTypecheck True = 0

-- ---------------------------------

instance Trav a => Trav [a] where
  type Block [a] = Block a
  trav _ []     = return ()
  trav f (x:xs) = trav f x >> trav f xs

instance Trav (MId, CExp o) where
  type Block (MId, CExp o) = RefInfo o
  trav f (_, ce) = trav f ce

instance Trav (TrBr a o) where
  type Block (TrBr a o) = RefInfo o
  trav f (TrBr es _) = trav f es

instance Trav (Exp o) where
  type Block (Exp o) = RefInfo o
  trav f = \case
    App _ _ _ args         -> trav f args
    Lam _ (Abs _ b)        -> trav f b
    Pi _ _ _ it (Abs _ ot) -> trav f it >> trav f ot
    Sort _                 -> return ()
    AbsurdLambda{}         -> return ()

instance Trav (ArgList o) where
  type Block (ArgList o) = RefInfo o
  trav _ ALNil               = return ()
  trav f (ALCons _ arg args) = trav f arg >> trav f args
  trav f (ALProj eas _ _ as) = trav f eas >> trav f as
  trav f (ALConPar args)     = trav f args

-- ---------------------------------
