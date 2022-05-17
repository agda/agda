
module Agda.Auto.Typecheck where

import Prelude hiding ((!!))

import Data.IORef

import Agda.Syntax.Common (Hiding (..))
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax
import Agda.Auto.SearchControl

import Agda.Utils.Impossible
import Agda.Utils.List

-- ---------------------------------

-- | Typechecker drives the solution of metas.
tcExp :: Bool -> Ctx o -> CExp o -> MExp o -> EE (MyPB o)
tcExp isdep ctx typ@(TrBr typtrs ityp@(Clos _ itypexp)) trm =
  mbpcase prioTypeUnknown Nothing (hnn_checkstep ityp) $ \(hntyp, iotastepdone) ->
  mmpcase (True, prioTypecheck isdep, Just (RIMainInfo (length ctx) hntyp iotastepdone)) trm $ \trm -> case trm of
   App _ okh elr args -> case rawValue hntyp of
    HNPi{} | isdep -> mpret $ Error "tcExp, dep terms should be eta-long"
    _ -> do
     (ityp, sc) <- case elr of
              Var v -> -- assuming within scope
               return (weak (v + 1) (snd $ ctx !! v), id)
              Const c -> do
               cdef <- readIORef c
               return (closify (cdtype cdef), \x -> mpret $ And (Just [Term args]) (noiotastep_term c args) x)

     ndfv <- case elr of
              Var{} -> return 0
              Const c -> readIORef c >>= \cd -> return (cddeffreevars cd)


     isconstructor <- case elr of
      Var{} -> return False
      Const c -> do
       cdef <- readIORef c
       return $ case cdcont cdef of {Constructor{} -> True; _ -> False}

     sc $ tcargs ndfv isdep ctx ityp args (NotM $ App Nothing (NotM OKVal) elr (NotM ALNil)) isconstructor $ \ityp _ -> mpret $ ConnectHandle okh (comp' True typ ityp)
   Lam hid (Abs id1 b) -> case rawValue hntyp of
    HNPi hid2 _ it (Abs id2 ot) | hid == hid2 ->
     tcExp isdep ((pickid id1 id2, t it) : ctx) (t ot) b
    _ -> mpret $ Error "tcExp, type of lam should be fun or pi (and same hid)"
   Pi _ _ _ it (Abs id ot) -> case rawValue hntyp of
    HNSort s ->
     mpret $ And (Just [Term ctx, Term it])
      (tcExp True ctx (closify (NotM $ Sort s)) it)
      (tcExp isdep ((id, closify it) : ctx) (closify (NotM $ Sort s)) ot)
    _ -> mpret $ Error "tcExp, type of pi should be set"
   Sort (Set i) -> case rawValue hntyp of
    HNSort s2 -> case s2 of
     Set j -> mpret $ if i < j then OK else Error "tcExp, type of set should be larger set"

     UnknownSort -> mpret OK -- mpret $ Error "tcExp, type of set i unknown sort" -- OK instead? (prev __IMPOSSIBLE__)

     Type -> mpret OK
    _ -> mpret $ Error "tcExp, type of set should be set"

   Sort UnknownSort -> __IMPOSSIBLE__

   Sort Type -> __IMPOSSIBLE__

   AbsurdLambda hid -> case rawValue hntyp of
    HNPi hid2 _ it _ | hid == hid2 ->
     mbpcase prioAbsurdLambda Nothing (getDatatype it) $ \res -> case res of
      Just (indeces, cons) ->
       foldl (\p con -> mpret $ And Nothing p (
        constructorImpossible indeces con
       )) (mpret OK) cons
      Nothing -> mpret $ Error "tcExp, absurd lambda, datatype needed"
    _ -> mpret $ Error "tcExp, type of absurd lam should be fun or pi (and same hid)"


  where
   t = TrBr typtrs


getDatatype :: ICExp o -> EE (MyMB (Maybe (ICArgList o, [ConstRef o])) o)
getDatatype t =
 mbcase (hnn t) $ \hnt -> case rawValue hnt of
  HNApp (Const c) args -> do
   cd <- readIORef c
   case cdcont cd of
    Datatype cons _ -> mbret $ Just (args, cons) -- ?? check that lenth args corresponds to type of datatype
    _ -> mbret Nothing
  _ -> mbret Nothing

constructorImpossible :: ICArgList o -> ConstRef o -> EE (MyPB o)
constructorImpossible args c = do
 cd <- readIORef c
 mbpcase prioAbsurdLambda Nothing (traversePi (-1) (Clos [] $ cdtype cd)) $ \hnot ->
  case rawValue hnot of
   HNApp _ args2 -> unequals args args2 (\_ -> mpret $ Error "not unequal") []
   _ -> mpret $ Error "constructorImpossible 1"

unequals :: ICArgList o -> ICArgList o -> ([(Nat, HNExp o)] -> EE (MyPB o)) -> [(Nat, HNExp o)] -> EE (MyPB o)
unequals es1 es2 cont unifier2 =
 mbpcase prioAbsurdLambda Nothing (hnarglist es1) $ \hnes1 ->
 mbpcase prioAbsurdLambda Nothing (hnarglist es2) $ \hnes2 ->
 case (hnes1, hnes2) of
  (HNALCons _ e1 es1, HNALCons _ e2 es2) -> unequal e1 e2 (unequals es1 es2 cont) unifier2

  (HNALConPar es1, HNALConPar es2) -> unequals es1 es2 cont unifier2

  _ -> cont unifier2

unequal :: ICExp o -> ICExp o -> ([(Nat, HNExp o)] -> EE (MyPB o)) -> [(Nat, HNExp o)] -> EE (MyPB o)
unequal e1 e2 cont unifier2 =
 mbpcase prioAbsurdLambda Nothing (hnn e1) $ \hne1 ->
 mbpcase prioAbsurdLambda Nothing (hnn e2) $ \hne2 ->
  case rawValue hne2 of
   HNApp (Var v2) es2 | v2 < 0 ->
    mbpcase prioAbsurdLambda Nothing (hnarglist es2) $ \hnes2 -> case hnes2 of
     HNALNil ->
      case lookup v2 unifier2 of
       Nothing -> cont ((v2, hne1) : unifier2)
       Just hne2' -> cc hne1 hne2'
     HNALCons{} -> cont unifier2

     HNALConPar{} -> __IMPOSSIBLE__

   _ -> cc hne1 hne2
 where
  cc hne1 hne2 = case (rawValue hne1, rawValue hne2) of
   (HNApp (Const c1) es1, HNApp (Const c2) es2) -> do
    cd1 <- readIORef c1
    cd2 <- readIORef c2
    case (cdcont cd1, cdcont cd2) of
     (Constructor{}, Constructor{}) ->
      if c1 == c2 then
       unequals es1 es2 cont unifier2
      else
       mpret OK
     _ -> cont unifier2
   _ -> cont unifier2

traversePi :: Int -> ICExp o -> EE (MyMB (HNExp o) o)
traversePi v t =
 mbcase (hnn t) $ \hnt ->
 case rawValue hnt of
  HNPi _ _ _ (Abs _ ot) -> traversePi (v - 1) $ subi (NotM $ App Nothing (NotM OKVal) (Var v) (NotM ALNil)) ot
  _ -> mbret hnt

tcargs :: Nat -> Bool -> Ctx o -> CExp o -> MArgList o -> MExp o -> Bool ->
          (CExp o -> MExp o -> EE (MyPB o)) -> EE (MyPB o)
tcargs ndfv isdep ctx ityp@(TrBr ityptrs iityp) args elimtrm isconstructor cont = mmpcase (True, prioTypecheckArgList, (Just $ RICheckElim $ isdep || isconstructor)) args $ \args' -> case args' of
 ALNil -> cont ityp elimtrm
 ALCons hid a as ->
  mbpcase prioInferredTypeUnknown (Just RIInferredTypeUnknown) (hnn iityp) $ \hnityp -> case rawValue hnityp of
   HNPi hid2 possdep it (Abs _ ot)
     | ndfv > 0 || copyarg a || hid == hid2 -> mpret $
    And (Just ([Term a | possdep] ++ [Term ctx, Term ityptrs]))
        (if ndfv > 0 then mpret OK else tcExp (isdep || possdep) ctx (t it) a)
        (tcargs (ndfv - 1) isdep ctx (sub a (t ot)) as (addend hid a elimtrm) isconstructor cont)
   _ -> mpret $ Error "tcargs, inf type should be fun or pi (and same hid)"


 ALProj{} | ndfv > 0 -> __IMPOSSIBLE__

 ALProj preas projidx hid as ->
  mbpcase prioInferredTypeUnknown (Just RIInferredTypeUnknown) (hnn iityp) $ \hnityp -> case rawValue hnityp of
   HNApp (Const dd) _ -> do
    dddef <- readIORef dd
    case cdcont dddef of
     Datatype _ projs ->
      mmpcase (True, prioProjIndex, Just (RICheckProjIndex projs)) projidx $
      \projidx -> do
       projd <- readIORef projidx
       tcargs (cddeffreevars projd) isdep ctx (closify $ cdtype projd) preas (NotM $ App Nothing (NotM OKVal) (Const projidx) (NotM ALNil)) True $
        \ityp2@(TrBr ityp2trs iityp2) elimtrm2 ->
         case iityp2 of
          Clos _ (NotM (Pi _ _ _ (NotM (App _ _ (Const dd2) _)) _)) | dd2 == dd ->
           mbpcase prioInferredTypeUnknown (Just RIInferredTypeUnknown) (hnn iityp2) $ \hnityp2 -> case rawValue hnityp2 of
            HNPi hid2 possdep it (Abs _ ot) | hid == hid2 -> mpret $
             And Nothing
                 (comp' True (TrBr ityp2trs it) ityp)
                 (tcargs 0 isdep ctx (sub elimtrm (t ot)) as (addend hid elimtrm elimtrm2) isconstructor cont)
            _ -> mpret $ Error "proj function type is not a Pi"
          _ -> mpret $ Error "proj function type is not correct"
     _ -> mpret $ Error "proj, not a datatype"
   _ -> mpret $ Error "proj, not a const app"


 ALConPar _ -> __IMPOSSIBLE__

 where
  t = TrBr ityptrs

addend :: Hiding -> MExp o -> MM (Exp o) blk -> MM (Exp o) blk
addend hid a (NotM (App uid okh elr as)) = NotM $ App uid okh elr (f as)
 where
   f (NotM ALNil)             = NotM $ ALCons hid a (NotM $ ALNil)
   f (NotM (ALCons hid a as)) = NotM $ ALCons hid a (f as)
   f _                        = __IMPOSSIBLE__
addend _ _ _ = __IMPOSSIBLE__

copyarg :: MExp o -> Bool
copyarg _ = False

-- ---------------------------------

type HNNBlks o = [HNExp o]

noblks :: HNNBlks o
noblks = []

addblk :: HNExp o -> HNNBlks o -> HNNBlks o
addblk = (:)

hnn :: ICExp o -> EE (MyMB (HNExp o) o)
hnn e = mbcase (hnn_blks e) $ \(hne, _) -> mbret hne

hnn_blks :: ICExp o -> EE (MyMB (HNExp o, HNNBlks o) o)
hnn_blks e = hnn' e CALNil

hnn_checkstep :: ICExp o -> EE (MyMB (HNExp o, Bool) o)
hnn_checkstep e =
 mbcase (hnb e CALNil) $ \hne ->
  mbcase (iotastep True hne) $ \res -> case res of
   Right _ -> mbret (hne, False)
   Left (e, as) ->
    mbcase (hnn' e as) $ \(hne, _) -> mbret (hne, True)


hnn' :: ICExp o -> ICArgList o -> EE (MyMB (HNExp o, HNNBlks o) o)
hnn' e as =
 mbcase (hnb e as) $ \hne ->
  mbcase (iotastep True hne) $ \res -> case res of
   Right blks -> mbret (hne, blks)
   Left (e, as) -> hnn' e as

hnb :: ICExp o -> ICArgList o -> EE (MyMB (HNExp o) o)
hnb e as = mbcase (hnc False e as []) $ \res -> case res of
            HNDone _ hne -> mbret hne
            HNMeta{} -> __IMPOSSIBLE__

data HNRes o = HNDone (Maybe (Metavar (Exp o) (RefInfo o))) (HNExp o)
             | HNMeta (ICExp o) (ICArgList o) [Maybe (UId o)]

hnc :: Bool -> ICExp o -> ICArgList o -> [Maybe (UId o)] -> EE (MyMB (HNRes o) o)
hnc haltmeta = loop
 where
  loop ce@(Clos cl e) cargs seenuids =
   (if haltmeta then mmmcase e (mbret $ HNMeta ce cargs seenuids) else mmcase e) $
   \ee -> case ee of
    App uid okh elr args ->
     let ncargs = CALConcat (Clos cl args) cargs
     in case elr of
      Var v -> case doclos cl v of
       Left v' -> mbret $ HNDone expmeta
                        $ WithSeenUIds (uid : seenuids)
                        $ HNApp (Var v') ncargs
       Right f -> loop f ncargs (uid : seenuids)
      Const _ -> mbret $ HNDone expmeta
                       $ WithSeenUIds (uid : seenuids)
                       $ HNApp elr ncargs
    Lam hid (Abs id b) ->
     mbcase (hnarglist cargs) $ \hncargs -> case hncargs of
      HNALNil -> mbret $ HNDone expmeta
                       $ WithSeenUIds seenuids
                       $ HNLam hid (Abs id (Clos (Skip : cl) b))
      HNALCons _ arg cargs' -> loop (Clos (Sub arg : cl) b) cargs' seenuids

      HNALConPar{} -> __IMPOSSIBLE__

    Pi uid hid possdep it (Abs id ot) ->
       checkNoArgs cargs $ mbret $ HNDone expmeta
         $ WithSeenUIds (uid : seenuids)
         $ HNPi hid possdep (Clos cl it) (Abs id (Clos (Skip : cl) ot))
    Sort s -> checkNoArgs cargs $ mbret
            $ HNDone expmeta $ WithSeenUIds [] $ HNSort s

    AbsurdLambda{} -> mbfailed "hnc: encountered absurdlambda"


   where expmeta = case e of {Meta m -> Just m; NotM _ -> Nothing}
  checkNoArgs cargs c =
   mbcase (hnarglist cargs) $ \hncargs -> case hncargs of
    HNALNil -> c
    HNALCons{} -> mbfailed "hnc: there should be no args"

    HNALConPar{} -> __IMPOSSIBLE__


hnarglist :: ICArgList o -> EE (MyMB (HNArgList o) o)
hnarglist args =
 case args of
  CALNil -> mbret HNALNil
  CALConcat (Clos cl args) args2 ->
   mmcase args $ \args -> case args of
    ALNil -> hnarglist args2
    ALCons hid arg argsb -> mbret $ HNALCons hid (Clos cl arg) (CALConcat (Clos cl argsb) args2)

    ALProj{} -> mbret HNALNil -- dirty hack to make check of no-iota in term work


    ALConPar args -> mbret $ HNALConPar (CALConcat (Clos cl args) args2)
-- -----------------------------

getNArgs :: Nat -> ICArgList o -> EE (MyMB (Maybe ([ICExp o], ICArgList o)) o)
getNArgs 0 args = mbret $ Just ([], args)
getNArgs narg args =
 mbcase (hnarglist args) $ \hnargs -> case hnargs of
  HNALNil -> mbret Nothing
  HNALCons _ arg args' ->
   mbcase (getNArgs (narg - 1) args') $ \res -> case res of
    Nothing -> mbret Nothing
    Just (pargs, rargs) -> mbret $ Just (arg : pargs, rargs)

  HNALConPar{} -> __IMPOSSIBLE__


getAllArgs :: ICArgList o -> EE (MyMB [ICExp o] o)
getAllArgs args =
 mbcase (hnarglist args) $ \hnargs -> case hnargs of
  HNALNil -> mbret []
  HNALCons _ arg args' ->
   mbcase (getAllArgs args') $ \args'' ->
    mbret (arg : args'')

  HNALConPar args2 ->
   mbcase (getAllArgs args2) $ \args3 -> mbret (__IMPOSSIBLE__ : args3)


data PEval o = PENo (ICExp o)
             | PEConApp (ICExp o) (ConstRef o) [PEval o]

iotastep :: Bool -> HNExp o -> EE (MyMB (Either (ICExp o, ICArgList o) (HNNBlks o)) o)
iotastep smartcheck e = case rawValue e of
 HNApp (Const c) args -> do
  cd <- readIORef c
  case cdcont cd of
   Def narg cls _ _ ->
    mbcase (getNArgs narg args) $ \res -> case res of
     Nothing -> mbret (Right noblks)
     Just (pargs, rargs) ->
      mbcase (dorules cls (map PENo pargs)) $ \res -> case res of
       Right blks -> mbret (Right blks)
       Left rhs -> mbret $ Left (rhs, rargs)
   _ -> mbret $ Right noblks
 _ -> mbret $ Right noblks
 where
 dorules :: [Clause o] -> [PEval o] -> EE (MyMB (Either (ICExp o) (HNNBlks o)) o)
 dorules [] _ = mbret $ Right noblks
 dorules (rule:rules') as =
  mbcase (dorule rule as) $ \x -> case x of
   Left (Left as') -> dorules rules' as'
   Left (Right blks) -> mbret (Right blks)
   Right rhs -> mbret $ Left rhs

 dorule :: Clause o -> [PEval o] -> EE (MyMB (Either (Either [PEval o] (HNNBlks o)) (ICExp o)) o)
 dorule (pats, rhs) as =
  mbcase (dopats pats as) $ \x -> case x of
   Right (_, ss) -> mbret $ Right (Clos (map Sub ss) rhs)
   Left hnas -> mbret $ Left hnas

 dopats :: [Pat o] -> [PEval o] -> EE (MyMB (Either (Either [PEval o] (HNNBlks o)) ([PEval o], [ICExp o])) o)
 dopats [] [] = mbret $ Right ([], [])
 dopats (p:ps') (a:as') =
  mbcase (dopat p a) $ \x -> case x of
   Right (hna, ss) ->
    mbcase (dopats ps' as') $ \x -> case x of
     Right (hnas, ss2) -> mbret $ Right (hna : hnas, ss2 ++ ss)
     Left (Right blks) -> mbret $ Left (Right blks)
     Left (Left hnas) -> mbret $ Left $ Left (hna : hnas)
   Left (Right blks) -> mbret $ Left (Right blks)
   Left (Left hna) -> mbret $ Left $ Left (hna : as')
 dopats _ _ = mbfailed "bad patterns"

 dopat :: Pat o -> PEval o -> EE (MyMB (Either (Either (PEval o) (HNNBlks o)) (PEval o, [ICExp o])) o)
 dopat (PatConApp c pas) a =
  case a of
   PENo a ->
    if smartcheck then
     mbcase (meta_not_constructor a) $ \notcon -> if notcon then mbret $ Left $ Right noblks else qq -- to know more often if iota step is possible
    else
     qq
    where
     qq =
      mbcase (hnn_blks a) $ \(hna, blks) -> case rawValue hna of
       HNApp (Const c') as ->
        if c == c' then
         mbcase (getAllArgs as) $ \as' ->
          if length as' == length pas then
           mbcase (dopats pas (map PENo as')) $ \x -> case x of
            Right (hnas, ss) -> mbret $ Right (PEConApp a c' hnas, ss)
            Left (Right blks) -> mbret $ Left (Right blks)
            Left (Left hnas) -> mbret $ Left $ Left (PEConApp a c' hnas)
          else
           mbfailed "dopat: wrong amount of args"
        else do
         cd <- readIORef c'
         case cdcont cd of
          Constructor{} -> mbcase (getAllArgs as) $ \as' ->
           mbret $ Left (Left (PEConApp a c' (map PENo as')))
          _ -> mbret $ Left (Right (addblk hna blks))
       _ -> mbret $ Left (Right (addblk hna blks))
   aa@(PEConApp a c' as) ->
    if c == c' then
     if length as == length pas then
      mbcase (dopats pas as) $ \x -> case x of
       Right (hnas, ss) -> mbret $ Right (PEConApp a c' hnas, ss)
       Left (Right blks) -> mbret $ Left (Right blks)
       Left (Left hnas) -> mbret $ Left $ Left (PEConApp a c' hnas)
     else
      mbfailed "dopat: wrong amount of args"
    else
     mbret $ Left (Left aa)
 dopat (PatProj cs) a =
  case a of
   PENo a ->
    if smartcheck then
     mbcase (meta_not_constructor a) $ \notcon -> if notcon then mbret $ Left $ Right noblks else qq -- to know more often if iota step is possible
    else
     qq
    where
     qq =
      mbcase (hnn_blks a) $ \(hna, blks) -> case rawValue hna of
       HNApp (Const c') as ->
        do
         cd <- readIORef c'
         case cdcont cd of
          Constructor{} -> mbcase (getAllArgs as) $ \as' ->
           mbret $ Left (Left (PEConApp a c' (map PENo as')))
          _ -> mbret $ Left (Right (addblk hna blks))
       _ -> mbret $ Left (Right (addblk hna blks))
   aa@(PEConApp a c' as) -> mbret $ Left (Left aa)
 dopat PatVar{} a@(PENo a') = mbret $ Right (a, [a'])
 dopat PatVar{} a@(PEConApp a' _ _) = mbret $ Right (a, [a'])
 dopat PatExp a = mbret $ Right (a, [])

-- -----------------------------

noiotastep :: HNExp o -> EE (MyPB o)
noiotastep hne =
 mbpcase prioNoIota Nothing (iotastep False hne) $ \res -> case res of
  Left _ -> mpret $ Error "iota step possible contrary to assumed"
  Right _ -> mpret OK

noiotastep_term :: ConstRef o -> MArgList o -> EE (MyPB o)
noiotastep_term c args = do
  cd <- readIORef c
  case cdcont cd of
    Def _ [(pats, _)] _ _ -> mpret OK
      -- all (\pat -> case pat of {PatConApp{} -> False; _ -> True}) pats
    _ -> noiotastep $ WithSeenUIds []
                    $ HNApp (Const c) $ CALConcat (Clos [] args) CALNil

data CMode o = CMRigid (Maybe (Metavar (Exp o) (RefInfo o))) (HNExp o)
             | forall b . Refinable b (RefInfo o) => CMFlex (MM b (RefInfo o)) (CMFlex o)
data CMFlex o = CMFFlex (ICExp o) (ICArgList o) [Maybe (UId o)]
              | CMFSemi (Maybe (Metavar (Exp o) (RefInfo o))) (HNExp o)
              | CMFBlocked (Maybe (Metavar (Exp o) (RefInfo o))) (HNExp o)

comp' :: forall o . Bool -> CExp o -> CExp o -> EE (MyPB o)
comp' ineq lhs@(TrBr trs1 e1) rhs@(TrBr trs2 e2) = comp ineq e1 e2
 where
  comp :: Bool -> ICExp o -> ICExp o -> EE (MyPB o)
  comp ineq e1 e2 =
   proc e1 e2

   where
    proc e1 e2 = f True e1 CALNil [] $ \res1 -> f True e2 CALNil [] $ \res2 -> g res1 res2
    f semifok e as seenuids cont =
     mbpcase prioCompBeta Nothing (hnc True e as seenuids) $ \res ->
      case res of
       HNDone mexpmeta hne -> fhn semifok mexpmeta hne cont

       HNMeta ce@(Clos cl m) cargs seenuids -> do
        b1 <- boringClos cl
        b2 <- boringArgs cargs
        if b1 && b2 then
          cont $ CMFlex m (CMFFlex ce cargs seenuids)
         else
          mbpcase prioCompBetaStructured Nothing (hnc False ce cargs seenuids) $ \res ->
           case res of
            HNDone mexpmeta hne -> cont $ CMFlex m (CMFBlocked mexpmeta hne)
            HNMeta{} -> __IMPOSSIBLE__


    fhn semifok mexpmeta hne cont =
     mmbpcase (iotastep True hne)
      (\m -> do
        let sf = False {- semiflex hne -}
        if semifok && sf then
          cont (CMFlex m (CMFSemi mexpmeta hne))
         else
          cont (CMFlex m (CMFBlocked mexpmeta hne))
      )
      (\res -> case res of
        Right _ -> cont (CMRigid mexpmeta hne)
        Left (e, as) -> f semifok e as [] cont
      )
    g res1 res2 =
     case (res1, res2) of
      (CMRigid mexpmeta1 hne1, CMRigid mexpmeta2 hne2) -> comphn ineq mexpmeta1 hne1 mexpmeta2 hne2
      (CMFlex m1 (CMFBlocked mexpmeta1 hne1), _) -> mstp False mexpmeta1 hne1 $ \res1 -> g res1 res2
      (_, CMFlex m2 (CMFBlocked mexpmeta2 hne2)) -> mstp False mexpmeta2 hne2 $ \res2 -> g res1 res2
      (CMRigid mexpmeta1 hne1, CMFlex _ fl2) -> unif True mexpmeta1 hne1 fl2
      (CMFlex _ fl1, CMRigid mexpmeta2 hne2) -> unif False mexpmeta2 hne2 fl1


      (CMFlex m1 fl1, CMFlex m2 fl2) -> doubleblock m1 m2 $ fcm fl1 $ \res1 -> fcm fl2 $ \res2 -> g res1 res2
    fcm (CMFFlex ce cargs seenuids) = f True ce cargs seenuids
    fcm (CMFSemi mexpmeta hne) = fhn True mexpmeta hne
    fcm (CMFBlocked _ hne) = __IMPOSSIBLE__ -- not used. if so should be: fhn False hne
    mstp semif mexpmeta hne cont =
     mpret $ Or prioCompChoice
      (mpret $ And (Just [Term lhs, Term rhs])
       (noiotastep hne)
       (cont (CMRigid mexpmeta hne))
      )
      (stp semif hne cont)
    stp semif hne cont =
     mbpcase prioCompIota (Just $ RIIotaStep semif) (iotastep True hne) $ \res -> case res of
      Right _ -> mpret $ Error "no iota step possible, contrary to assumed"
      Left (e, as) -> f semif e as [] cont
    unif oppis1 oppmexpmeta opphne res =
     let iter res = if oppis1 then
                     g (CMRigid oppmexpmeta opphne) res
                    else
                     g res (CMRigid oppmexpmeta opphne)
     in case res of
      CMFFlex ce cargs seenuids -> do
       poss <- iotapossmeta ce cargs
       maybeor poss prioCompChoice
        (loop ce cargs seenuids)
-- (mbpcase prioCompBeta (Just $ RIIotaStep False) (hnb ce cargs) $ \hne ->
        (mbpcase prioCompBeta (Just $ RIIotaStep False) (hnc False ce cargs seenuids) $ \res ->
          -- RIIotaStep here on beta-norm to make cost high when guessing elim const in type par
          case res of
           HNDone mexpmeta hne -> stp False hne iter
           HNMeta{} -> __IMPOSSIBLE__
        )
       where
        loop ce@(Clos cl m) cargs seenuids =
         mmpcase (False, prioCompUnif, Just (RIUnifInfo cl opphne)) m $ \_ ->
         mbpcase prioCompBeta Nothing (hnc True ce cargs seenuids) $ \res -> case res of
          HNDone mexpmeta hne ->
           mpret $ And (Just [Term lhs, Term rhs])
            (noiotastep hne)
            (iter (CMRigid mexpmeta hne))
          HNMeta ce cargs seenuids -> loop ce cargs seenuids
      CMFSemi _ hne ->
       __IMPOSSIBLE__ -- CMFSemi disabled, if used should be: stp True hne iter
      CMFBlocked{} -> __IMPOSSIBLE__
    comphn :: Bool -> Maybe (Metavar (Exp o) (RefInfo o)) -> HNExp o -> Maybe (Metavar (Exp o) (RefInfo o)) -> HNExp o -> EE (MyPB o)
    comphn ineq mexpmeta1 hne1 mexpmeta2 hne2 =
     case (rawValue hne1, rawValue hne2) of
      (HNApp elr1 args1, HNApp elr2 args2) ->
       let ce = case (elr1, elr2) of
                 (Var v1, Var v2) ->
                     if v1 == v2 then Nothing
                     else Just "comphn, elr, vars not equal"
                 (Const c1, Const c2) ->
                    if c1 == c2 then Nothing
                    else Just "comphn, elr, consts not equal"
                 (_, _) -> Just "comphn, elrs not equal"
       in case ce of
            Nothing -> compargs args1 args2
            Just msg -> mpret $ Error msg
      (HNLam hid1 (Abs id1 b1), HNLam hid2 (Abs id2 b2)) -> comp False b1 b2
      (HNLam _ (Abs _ b1), HNApp elr2 args2) ->
       f True b1 CALNil (seenUIds hne1) $ \res1 ->
       fhn True mexpmeta2 (WithSeenUIds (seenUIds hne2) $ HNApp (weak 1 elr2) (addtrailingargs (Clos [] $ NotM $ ALCons NotHidden{- arbitrary -} (NotM $ App Nothing (NotM OKVal) (Var 0) (NotM ALNil)) (NotM ALNil)) (weak 1 args2))) $ \res2 -> g res1 res2
      (HNApp elr1 args1, HNLam _ (Abs _ b2)) ->
       fhn True mexpmeta1 (WithSeenUIds (seenUIds hne1) $ HNApp (weak 1 elr1) (addtrailingargs (Clos [] $ NotM $ ALCons NotHidden{- arbitrary -} (NotM $ App Nothing (NotM OKVal) (Var 0) (NotM ALNil)) (NotM ALNil)) (weak 1 args1))) $ \res1 -> f True b2 CALNil (seenUIds hne2) $ \res2 -> g res1 res2
{-
      (HNLam _ (Abs _ b1), HNApp uid2 elr2 args2) ->
       f True b1 CALNil $ \res1 -> g res1
        (CMRigid mexpmeta2 (HNApp uid2 (weak 1 elr2) (addtrailingargs (Clos [] $ NotM $ ALCons NotHidden{- arbitrary -} (NotM $ App Nothing (NotM OKVal) (Var 0) (NotM ALNil)) (NotM ALNil)) (weak 1 args2))))
      (HNApp uid1 elr1 args1, HNLam _ (Abs _ b2)) ->
       f True b2 CALNil $ \res2 -> g
        (CMRigid mexpmeta1 (HNApp uid1 (weak 1 elr1) (addtrailingargs (Clos [] $ NotM $ ALCons NotHidden{- arbitrary -} (NotM $ App Nothing (NotM OKVal) (Var 0) (NotM ALNil)) (NotM ALNil)) (weak 1 args1))))
        res2
-}
      (HNPi hid1 _ it1 (Abs id1 ot1), HNPi hid2 _ it2 (Abs id2 ot2)) -> mpret $
       And (Just [Term trs1, Term trs2]) (comp False it1 it2) (comp ineq ot1 ot2)
      (HNSort s1, HNSort s2) -> mpret $
       case (s1, s2) of
        (Set i1, Set i2) -> if i1 == i2 || ineq && i1 > i2 then OK else Error "comphn, set levels not matching"
        (Set _, UnknownSort) -> OK
        (UnknownSort, Set _) -> OK
        (UnknownSort, UnknownSort) -> OK
        (Type, Set _) | ineq -> OK
        (Type, UnknownSort) | ineq -> OK
        _ -> __IMPOSSIBLE__
      (HNApp (Const c1) _, _) -> case mexpmeta2 of
       Nothing -> mpret $ Error "comphn, not equal (2)"
       Just m2 -> mpret $ AddExtraRef "comphn: not equal, adding extra ref"
                          m2 (extraref m2 (seenUIds hne1) c1)
      (_, HNApp (Const c2) _) -> case mexpmeta1 of
       Nothing -> mpret $ Error "comphn, not equal (3)"
       Just m1 -> mpret $ AddExtraRef "comphn: not equal, adding extra ref"
                          m1 (extraref m1 (seenUIds hne2) c2)
      (_, _) -> mpret $ Error "comphn, not equal"

    compargs :: ICArgList o -> ICArgList o -> EE (MyPB o)
    compargs args1 args2 =
     mbpcase prioCompareArgList Nothing (hnarglist args1) $ \hnargs1 ->
     mbpcase prioCompareArgList Nothing (hnarglist args2) $ \hnargs2 ->
     case (hnargs1, hnargs2) of
      (HNALNil, HNALNil) -> mpret OK
      (HNALCons hid1 arg1 args1b, HNALCons hid2 arg2 args2b) -> mpret $
       And (Just [Term trs1, Term trs2]) (comp False arg1 arg2) (compargs args1b args2b)

      (HNALConPar args1b, HNALCons _ _ args2b) -> compargs args1b args2b
      (HNALCons _ _ args1b, HNALConPar args2b) -> compargs args1b args2b
      (HNALConPar args1', HNALConPar args2') -> compargs args1' args2'

      (_, _) -> mpret $ Error $ "comphnargs, not equal"


    boringExp :: ICExp o -> EE Bool
    boringExp (Clos cl e) = do
     e <- expandbind e
     case e of
      Meta{} -> boringClos cl
      NotM e -> case e of
       App _ _ (Var v) as -> do
        as <- expandbind as
        case as of
         Meta{} -> return False
         NotM as -> case as of
          ALNil -> case doclos cl v of
           Left _ -> return True
           Right e -> boringExp e
          ALCons{} -> return False
          ALProj{} -> return False
          ALConPar{} -> return False

       _ -> return False

    boringClos :: [CAction o] -> EE Bool
    boringClos cl = and <$> mapM f cl
     where f (Sub e) = boringExp e
           f Skip = return True
           f (Weak _) = return True

    boringArgs :: ICArgList o -> EE Bool
    boringArgs CALNil = return True
    boringArgs (CALConcat (Clos cl as) as2) = do
     b1 <- f cl as
     b2 <- boringArgs as2
     return $ b1 && b2
     where
      f cl as = do
       as <- expandbind as
       case as of
        Meta{} -> return False
        NotM as -> case as of
         ALNil -> return True
         ALCons _ a as -> do
          b1 <- boringExp (Clos cl a)
          b2 <- f cl as
          return $ b1 && b2

         ALProj{} -> return False  -- Not impossible: #2966


         ALConPar as -> f cl as
-- ---------------------------------

checkeliminand :: MExp o -> EE (MyPB o)
checkeliminand = f [] []
 where
  f uids used e =
   mmpcase (False, prioNo, Just (RIUsedVars uids used)) e $ \e -> case e of
    App uid _ elr@(Var{}) args -> fs (adduid uid uids) (elr : used) args
    App uid _ elr@(Const c) args -> do
     cd <- readIORef c
     case cdcont cd of
      Def _ _ (Just i) _ -> mpret $ Sidecondition (fs (adduid uid uids) (elr : used) args) (g i args)
       where
        g i as = mmpcase (False, prioNo, Nothing) as $ \as -> case as of
                  ALNil -> mpret OK
                  ALCons _ a as -> case i of
                   0 -> mmpcase (False, prioNo, Just RINotConstructor) a $ \_ ->
                         mpret OK
                   _ -> g (i - 1) as

                  ALProj eas _ _ as -> mpret OK


                  ALConPar as -> case i of
                   0 -> __IMPOSSIBLE__
                   _ -> g (i - 1) as

      _ -> fs (adduid uid uids) (elr : used) args
    Lam _ (Abs _ e) -> f uids (w used) e
    Pi uid _ _ e1 (Abs _ e2) -> mpret $ Sidecondition (f (adduid uid uids) used e1) (f (adduid uid uids) (w used) e2)
    Sort _ -> mpret OK

    AbsurdLambda{} -> mpret OK


  fs uids used as =
   mmpcase (False, prioNo, Nothing) as $ \as -> case as of
    ALNil -> mpret OK
    ALCons _ a as -> mpret $ Sidecondition (f uids used a) (fs uids used as)

    ALProj eas _ _ as -> mpret $ Sidecondition (fs uids used eas) (fs uids used as)


    ALConPar as -> fs uids used as

  w = map (\x -> case x of {Var v -> Var (v + 1); Const{} -> x})
  adduid (Just uid) uids = uid : uids
  adduid Nothing uids = uids

-- ---------------------------------

maybeor :: Bool -> Prio -> IO (PB (RefInfo o)) -> IO (PB (RefInfo o)) ->
           IO (PB (RefInfo o))
maybeor _ _ mainalt _ = mainalt

iotapossmeta :: ICExp o -> ICArgList o -> EE Bool
iotapossmeta ce@(Clos cl _) cargs = do
 xs <- mapM ncaction cl
 y <- nccargs cargs
 return $ not (and xs && y)
 where
  ncaction (Sub ce) = nonconstructor ce
  ncaction Skip = return True
  ncaction (Weak{}) = return True
  nccargs CALNil = return True
  nccargs (CALConcat (Clos cl margs) cargs) = do
   x <- ncmargs cl margs
   y <- nccargs cargs
   return $ x && y
  ncmargs cl (Meta m) = do
   mb <- readIORef (mbind m)
   case mb of
    Nothing -> return False
    Just x -> ncargs cl x
  ncmargs cl (NotM args) = ncargs cl args
  ncargs cl ALNil = return True
  ncargs cl (ALCons _ a args) = do
   x <- nonconstructor (Clos cl a)
   y <- ncmargs cl args
   return $ x && y

  ncargs _ (ALProj{}) = __IMPOSSIBLE__


  ncargs cl (ALConPar args) = ncmargs cl args

  nonconstructor :: ICExp o -> EE Bool
  nonconstructor ce = do
   res <- hnc True ce CALNil []
   case res of
    Blocked{} -> return False
    Failed{} -> return False
    NotB res -> case res of
     HNMeta ce _ _ -> do
      let (Clos _ (Meta m)) = ce
      infos <- extractblkinfos m
      if any (\info -> case info of {RINotConstructor -> True; _ -> False}) infos then do
        return True
       else
        return False
      -- return False -- return True -- ?? removes completeness - Yes, in DavidW1.additionRight
     HNDone{} -> do
      res <- hnn ce
      case res of
       NotB hne -> case rawValue hne of
        HNApp (Const c) _ -> do
         cd <- readIORef c
         case cdcont cd of
          Constructor{} -> return False
          _ -> return True
        _ -> return True
       Blocked m _ -> return False -- not necessary to do check here because already done by hnn (!! if it's known that m stands for an eliminator then it cannot be constructor so True instead)
       Failed _ -> return False

meta_not_constructor :: ICExp o -> EE (MB Bool (RefInfo o))
meta_not_constructor a =
 mbcase (hnc True a CALNil []) $ \res -> case res of
  HNMeta ce _ _ -> do
    let (Clos _ (Meta m)) = ce
    infos <- extractblkinfos m
    if any (\info -> case info of {RINotConstructor -> True; _ -> False}) infos then do
      b <- iotapossmeta ce CALNil
      mbret $ not b
     else
      mbret False
  HNDone{} -> mbret False

-- ---------------------------------

calcEqRState :: EqReasoningConsts o -> MExp o -> EE (MyPB o)
calcEqRState cs = f EqRSNone
 where
  f s e =
   mmpcase (False, prioNo, Just (RIEqRState s)) e $ \e -> case e of
    App _ _ (Const c) args -> case () of
     _ | c == eqrcBegin cs -> fs [EqRSNone, EqRSNone, EqRSNone, EqRSNone, EqRSChain] args
     _ | c == eqrcStep cs -> fs [EqRSNone, EqRSNone, EqRSNone, EqRSNone, EqRSNone, EqRSPrf1, EqRSChain] args
     _ | c == eqrcSym cs -> fs [EqRSNone, EqRSNone, EqRSNone, EqRSNone, EqRSPrf2] args
     _ | c == eqrcCong cs -> fs [EqRSNone, EqRSNone, EqRSNone, EqRSNone, EqRSNone, EqRSNone, EqRSNone, EqRSPrf3] args
     _ -> fs [] args
    App _ _ (Var{}) args -> fs [] args
    Lam _ (Abs _ b) -> f EqRSNone b
    Pi _ _ _ it (Abs _ ot) -> mpret $ Sidecondition (f EqRSNone it) (f EqRSNone ot)
    Sort{} -> mpret OK

    AbsurdLambda{} -> mpret OK


  fs ss args =
   mmpcase (False, prioNo, Nothing) args $ \args -> case (ss, args) of
    (_, ALNil) -> mpret OK
    (s : ss, ALCons _ a args) -> mpret $ Sidecondition (f s a) (fs ss args)
    ([], ALCons _ a args) -> mpret $ Sidecondition (f EqRSNone a) (fs [] args)

    (_, ALProj eas _ _ as) -> mpret $ Sidecondition (fs [] eas) (fs [] as) -- when eqr-hint is given manually, ss can be non-empty here


    (_ : ss, ALConPar args) -> fs ss args
    ([], ALConPar args) -> fs [] args

-- ---------------------------------

pickid :: MId -> MId -> MId
pickid mid1@(Id _) _ = mid1
pickid _ mid2 = mid2

-- ---------------------------------

tcSearch :: Bool -> Ctx o -> CExp o -> MExp o -> EE (MyPB o)
tcSearch isdep ctx typ trm = mpret $ Sidecondition (checkeliminand trm)
                              (tcExp isdep ctx typ trm)

-- ----------------------------
