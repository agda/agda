{-# OPTIONS -fglasgow-exts #-}

module Agda.Auto.Typecheck where

import Data.IORef

import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax
import Agda.Auto.SearchControl

import Agda.Auto.Print  -- for debugging


closify :: a -> Clos a o
closify = Clos []

sub :: CExp o -> Clos a o -> Clos a o
-- sub e (Clos [] x) = Clos [Sub e] x
sub e (Clos (Skip : as) x) = Clos (Sub e : as) x
{-sub e (Clos (Weak n : as) x) = if n == 1 then
                                Clos as x
                               else
                                Clos (Weak (n - 1) : as) x-}
sub _ _ = error "sub: pattern not matched"

msubs :: [CExp o] -> a -> Clos a o
msubs ss x = Clos (map Sub ss) x

weak :: Nat -> Clos a o -> Clos a o
weak 0 x = x
weak n (Clos as x) = Clos (Weak n : as) x

{- -- only used by eta-conversion
weakarglist :: Nat -> CArgList -> CArgList
weakarglist 0 = id
weakarglist n = f
 where f CALNil = CALNil
       f (CALConcat cl as as2) = CALConcat (Weak n : cl) as (f as2)

weakelr :: Nat -> Elr -> Elr
weakelr 0 elr = elr
weakelr n (Var v) = Var (v + n)
weakelr _ elr@(Const _) = elr
-}

-- ---------------------------------

tcExp :: Bool -> Ctx o -> CExp o -> MExp o -> EE (MyPB o)
tcExp isdep ctx typ trm =
 mbpcase prioTypeUnknown (hnn typ) $ \hntyp ->
 mmpcase (True, prioTypecheck isdep, Just (RIMainInfo (length ctx) hntyp)) trm $ \trm -> case trm of
  App elr args -> do
   (ityp, sc) <- case elr of
            Var v ->  -- assuming within scope
             return (weak (v + 1) (snd $ ctx !! v), id)
            Const c -> do
             cdef <- readIORef c
             return (closify (cdtype cdef), \x -> mpret $ And (Just [Term args]) (noiotastep' c args) x)
   sc $ tcargs isdep ctx typ ityp args
  Lam hid (Abs id1 b) -> case hntyp of
   HNFun hid' it ot | hid == hid' ->
    tcExp isdep ((id1, it) : ctx) (weak 1 ot) b
   HNPi hid' it (Abs id2 ot) | hid == hid' ->
    tcExp isdep ((pickid id1 id2, it) : ctx) ot b
   _ -> mpret $ Error "tcExp, type of lam should be fun or pi (and same hid)"
  Fun _ it ot -> case hntyp of
   HNSort s ->
    mpret $ And (Just [Term ctx])
     (tcExp isdep ctx (closify (NotM $ Sort s)) it)
     (tcExp isdep ctx (closify (NotM $ Sort s)) ot)
   _ -> mpret $ Error "tcExp, type of fun should be set"
  Pi _ it (Abs id ot) -> case hntyp of
   HNSort s ->
    mpret $ And (Just [Term ctx, Term it])
     (tcExp True ctx (closify (NotM $ Sort s)) it)
     (tcExp isdep ((id, closify it) : ctx) (closify (NotM $ Sort s)) ot)
   _ -> mpret $ Error "tcExp, type of pi should be set"
  Sort (SortLevel i) -> case hntyp of
   HNSort s2 -> case s2 of
    SortLevel j -> mpret $ if i < j then OK else Error "tcExp, type of set should be larger set"
    Type -> mpret OK
   _ -> mpret $ Error "tcExp, type of set should be set"
  Sort Type -> error "tcexp: Sort Type should not occur"

tcargs :: Bool -> Ctx o -> CExp o -> CExp o -> MArgList o -> EE (MyPB o)
tcargs isdep ctx etyp ityp args = mmpcase (True, prioTypecheckArgList, Nothing) args $ \args -> case args of
 ALNil -> comp' etyp ityp
 ALCons hid a as ->
  mbpcase prioInferredTypeUnknown (hnn ityp) $ \hnityp -> case hnityp of
   HNFun hid' it ot | hid == hid' -> mpret $
    And (Just [Term ctx])
        (tcExp isdep ctx it a)
        (tcargs isdep ctx etyp ot as)
   HNPi hid' it (Abs _ ot) | hid == hid' -> mpret $
    And (Just [Term ctx, Term a])
        (tcExp True ctx it a)
        (tcargs isdep ctx etyp (sub (closify a) ot) as)
   _ -> mpret $ Error "tcargs, inf type should be fun or pi (and same hid)"
 ALConPar _ -> error "ConPar should not occur here"

-- ---------------------------------

hnn :: CExp o -> EE (MyMB (HNExp o) o)
hnn e = hnn' e CALNil

hnn' :: CExp o -> CArgList o -> EE (MyMB (HNExp o) o)
hnn' e as =
 mbcase (hn' e as) $ \hne ->
  mbcase (iotastep hne) $ \res -> case res of
   Nothing -> mbret hne
   Just (e, as) -> hnn' e as

hn' :: CExp o -> CArgList o -> EE (MyMB (HNExp o) o)
hn' e as = mbcase (hnc False e as) $ \res -> case res of
            HNDone hne -> mbret hne
            HNMeta _ _ -> error "hn': should not happen"

data HNRes o = HNDone (HNExp o)
             | HNMeta (CExp o) (CArgList o)

hnc :: Bool -> CExp o -> CArgList o -> EE (MyMB (HNRes o) o)
hnc haltmeta = loop
 where
  loop ce@(Clos cl e) cargs =
   (if haltmeta then mmmcase e (mbret $ HNMeta ce cargs) else mmcase e) $
   \e -> case e of
    App elr args ->
     let cargs' = CALConcat (Clos cl args) cargs
     in  case elr of
      Var v -> case doclos cl v of
       Left v' -> mbret $ HNDone $ HNApp (Var v') cargs'
       Right f -> loop f cargs'
      Const _ -> mbret $ HNDone $ HNApp elr cargs'
    Lam _ (Abs id b) ->
     let cb = Clos (Skip : cl) b
     in  mbcase (hnarglist cargs) $ \hncargs -> case hncargs of
      HNALNil -> mbret $ HNDone $ HNLam (Abs id cb)
      HNALCons arg cargs' -> loop (sub arg cb) cargs'
      HNALConPar _ -> error "ConPar should not occur here"
    Fun hid it ot -> checkNoArgs cargs $ mbret $ HNDone $ HNFun hid (Clos cl it) (Clos cl ot)
    Pi hid it (Abs id ot) -> checkNoArgs cargs $ mbret $ HNDone $ HNPi hid (Clos cl it) (Abs id (Clos (Skip : cl) ot))
    Sort s -> checkNoArgs cargs $ mbret $ HNDone $ HNSort s
  checkNoArgs cargs c =
   mbcase (hnarglist cargs) $ \hncargs -> case hncargs of
    HNALNil -> c
    HNALCons _ _ -> mbfailed "hnc: there should be not args"
    HNALConPar _ -> error "ConPar should not occur here"

doclos :: [CAction o] -> Nat -> Either Nat (CExp o)
doclos = f 0
 where
  f ns [] i = Left (ns + i)
  f ns (Weak n : xs) i = f (ns + n) xs i
  f ns (Skip : _) 0 = Left ns
  f ns (Sub s : _) 0 = Right (weak ns s)
  f ns (Skip : xs) i = f (ns + 1) xs (i - 1)
  f ns (Sub _ : xs) i = f ns xs (i - 1)

hnarglist :: CArgList o -> EE (MyMB (HNArgList o) o)
hnarglist args = case args of
 CALNil -> mbret HNALNil
 CALConcat (Clos cl args) args2 -> mmcase args $ \args -> case args of
   ALNil -> hnarglist args2
   ALCons _ arg args' -> mbret $ HNALCons (Clos cl arg) (CALConcat (Clos cl args') args2)
   ALConPar args' -> mbret $ HNALConPar (CALConcat (Clos cl args') args2)


-- -----------------------------

getNArgs :: Nat -> CArgList o -> EE (MyMB (Maybe ([CExp o], CArgList o)) o)
getNArgs 0 args = mbret $ Just ([], args)
getNArgs narg args =
 mbcase (hnarglist args) $ \hnargs -> case hnargs of
  HNALNil -> mbret Nothing
  HNALCons arg args' ->
   mbcase (getNArgs (narg - 1) args') $ \res -> case res of
    Nothing -> mbret Nothing
    Just (pargs, rargs) -> mbret $ Just (arg : pargs, rargs)
  HNALConPar _ -> error "ConPar should not occur here"

getAllArgs :: CArgList o -> EE (MyMB [PEval o] o)
getAllArgs args =
 mbcase (hnarglist args) $ \hnargs -> case hnargs of
  HNALNil -> mbret []
  HNALCons arg args' ->
   mbcase (getAllArgs args') $ \args'' ->
    mbret (PENo arg : args'')
  HNALConPar args' ->
   mbcase (getAllArgs args') $ \args'' ->
    mbret (PEConPar : args'')

iotastep :: HNExp o -> EE (MyMB (Maybe (CExp o, CArgList o)) o)
iotastep e = case e of
 HNApp (Const c) args -> do
  cd <- readIORef c
  case cdcont cd of
   Def narg cls ->
    mbcase (getNArgs narg args) $ \res -> case res of
     Nothing -> mbret Nothing
     Just (pargs, rargs) ->
      mbcase (dorules cls (map PENo pargs)) $ \res -> case res of
       Nothing -> mbret Nothing
       Just rhs -> mbret $ Just (rhs, rargs)
   _ -> mbret Nothing
 _ -> mbret Nothing

data PEval o = PENo (CExp o)
             | PEConApp (CExp o) (ConstRef o) [PEval o]
             | PEConPar

dorules :: [Clause o] -> [PEval o] -> EE (MyMB (Maybe (CExp o)) o)
dorules [] _ = mbret Nothing
dorules (rule:rules') as =
 mbcase (dorule rule as) $ \x -> case x of
  Left (Just as') -> dorules rules' as'
  Left Nothing -> mbret Nothing
  Right rhs -> mbret $ Just rhs

dorule :: Clause o -> [PEval o] -> EE (MyMB (Either (Maybe [PEval o]) (CExp o)) o)
dorule (pats, rhs) as =
 mbcase (dopats pats as) $ \x -> case x of
  Right (_, ss) -> mbret $ Right (msubs ss rhs)
  Left hnas -> mbret $ Left hnas

dopats :: [Pat o] -> [PEval o] -> EE (MyMB (Either (Maybe [PEval o]) ([PEval o], [CExp o])) o)
dopats [] [] = mbret $ Right ([], [])
dopats (p:ps') (a:as') =
 mbcase (dopat p a) $ \x -> case x of
  Right (hna, ss) ->
   mbcase (dopats ps' as') $ \x -> case x of
    Right (hnas, ss2) -> mbret $ Right (hna : hnas, ss2 ++ ss)
    Left Nothing -> mbret $ Left Nothing
    Left (Just hnas) -> mbret $ Left $ Just (hna : hnas)
  Left Nothing -> mbret $ Left Nothing
  Left (Just hna) -> mbret $ Left $ Just (hna : as')
dopats _ _ = error "dopats: pattern not matched"

dopat :: Pat o -> PEval o -> EE (MyMB (Either (Maybe (PEval o)) (PEval o, [CExp o])) o)
dopat (PatConApp c pas) a =
 case a of
  PENo a -> mbcase (hnn a) $ \hna -> case hna of
   HNApp (Const c') as ->
    if c == c' then
     mbcase (getAllArgs as) $ \as' ->
      if length as' == length pas then
       mbcase (dopats pas as') $ \x -> case x of
        Right (hnas, ss) -> mbret $ Right (PEConApp a c' hnas, ss)
        Left Nothing -> mbret $ Left Nothing
        Left (Just hnas) -> mbret $ Left $ Just (PEConApp a c' hnas)
      else
       mbfailed "dopat: wrong amount of args"
    else do
     cd <- readIORef c'
     case cdcont cd of
      Constructor -> mbcase (getAllArgs as) $ \as' ->
       mbret $ Left (Just (PEConApp a c' as'))
      _ -> mbret $ Left Nothing
   _ -> mbret $ Left Nothing
  aa@(PEConApp a c' as) ->
   if c == c' then
    if length as == length pas then
     mbcase (dopats pas as) $ \x -> case x of
      Right (hnas, ss) -> mbret $ Right (PEConApp a c' hnas, ss)
      Left Nothing -> mbret $ Left Nothing
      Left (Just hnas) -> mbret $ Left $ Just (PEConApp a c' hnas)
    else
     mbfailed "dopat: wrong amount of args"
   else
    mbret $ Left (Just aa)
  PEConPar -> error "ConPar should not occur here"
dopat PatVar a@(PENo a') = mbret $ Right (a, [a'])
dopat PatVar a@(PEConApp a' _ _) = mbret $ Right (a, [a'])
dopat PatVar PEConPar = error "ConPar should not occur here"
dopat PatExp a = mbret $ Right (a, [])

-- -----------------------------

noiotastep :: HNExp o -> EE (MyPB o)
noiotastep hne =
 mbpcase prioNo (iotastep hne) $ \res -> case res of
  Just _ -> mpret $ Error "iota step possible contrary to assumed"
  Nothing -> mpret OK

noiotastep' :: ConstRef o -> MArgList o -> EE (MyPB o)
noiotastep' c args = noiotastep $ HNApp (Const c) (CALConcat (Clos [] args) CALNil)


comp' :: CExp o -> CExp o -> EE (MyPB o)
comp' = comp True


comp :: Bool -> CExp o -> CExp o -> EE (MyPB o)
comp ineq e1 e2 = f e1 CALNil $ \res1 -> f e2 CALNil $ \res2 -> g res1 res2
 where
  f e as cont =
   mbpcase prioPreCompare (hnc True e as) $ \res ->
    case res of
     HNDone hne ->
      mmbpcase (iotastep hne)
       (mpret $ Or prioCompChoice
        (mpret $ And Nothing
         (noiotastep hne)
         (cont res)
        )
        (mbpcase prioCompIota (iotastep hne) $ \res -> case res of
         Nothing -> mpret $ Error "no iota step possibly, contrary to assumed"
         Just (e, as) -> f e as cont
        )
       )
       (\res' -> case res' of
         Nothing -> cont res
         Just (e, as) -> f e as cont
       )
     HNMeta _ _ -> cont res
  g res1 res2 =
   case (res1, res2) of
    (HNDone hne1, HNDone hne2) -> comphn' ineq hne1 hne2
    (HNDone hne1, HNMeta ce2 cargs2) -> unif True hne1 ce2 cargs2
    (HNMeta ce1 cargs1, HNDone hne2) -> unif False hne2 ce1 cargs1
    (HNMeta ce1@(Clos _ m1) cargs1, HNMeta ce2@(Clos _ m2) cargs2) -> doubleblock m1 m2 $ f ce1 cargs1 $ \res1 -> f ce2 cargs2 $ \res2 -> g res1 res2
  unif oppis1 opphne = loop
   where
    loop ce@(Clos cl m) cargs =
     do
      let Meta mm = m
      mmpcase (False, prioCompare, Just (RIUnifInfo mm cl opphne)) m $ \_ ->
       f ce cargs $ \res ->
        case res of
         HNDone hne -> if oppis1 then comphn' ineq opphne hne else comphn' ineq hne opphne
         HNMeta ce' cargs' -> loop ce' cargs'


comphn' :: Bool -> HNExp o -> HNExp o -> EE (MyPB o)
comphn' ineq hne1 hne2 =
 case (hne1, hne2) of
  (HNApp elr1 args1, HNApp elr2 args2) ->
   let ce = case (elr1, elr2) of
             (Var v1, Var v2) -> if v1 == v2 then Nothing else Just "comphn, elr, vars not equal"
             (Const c1, Const c2) -> if c1 == c2 then Nothing else Just "comphn, elr, consts not equal"
             (_, _) -> Just "comphn, elrs not equal"
   in  case ce of
        Nothing -> compargs args1 args2
        Just msg -> mpret $ Error msg
  (HNLam (Abs id1 b1), HNLam (Abs id2 b2)) -> comp False b1 b2
{- eta-conversion disabled
  (HNLam (Abs id b), HNApp elr args) ->
   mbpcase False prioCompare (hn b) $ \hnb ->
   comphn False (id : idctx) hnb (HNApp (weakelr 1 elr) (CALConcat (weakarglist 1 args) (CALCons (closify (NotM $ App (Var 0) $ NotM ALNil)) CALNil)))
  (HNApp elr args, HNLam (Abs id b)) ->
   mbpcase False prioCompare (hn b) $ \hnb ->
   comphn False (id : idctx) (HNApp (weakelr 1 elr) (CALConcat (weakarglist 1 args) (CALCons (closify (NotM $ App (Var 0) $ NotM ALNil)) CALNil))) hnb
-}
  (HNFun hid1 it1 ot1, HNFun hid2 it2 ot2) | hid1 == hid2 -> mpret $
   And (Just []) (comp False it1 it2) (comp ineq ot1 ot2)
  (HNPi hid1 it1 (Abs id1 ot1), HNPi hid2 it2 (Abs id2 ot2)) | hid1 == hid2 -> mpret $
   And (Just []) (comp False it1 it2) (comp ineq ot1 ot2)
  (HNFun hid1 it1 ot1, HNPi hid2 it2 (Abs id ot2)) | hid1 == hid2 -> mpret $  -- ?? exclude this case
   And (Just []) (comp False it1 it2) (comp ineq (weak 1 ot1) ot2)
  (HNPi hid1 it1 (Abs id ot1), HNFun hid2 it2 ot2) | hid1 == hid2 -> mpret $  -- ?? exclude this case
   And (Just []) (comp False it1 it2) (comp ineq ot1 (weak 1 ot2))
  (HNSort s1, HNSort s2) -> mpret $
   case (s1, s2) of
    (SortLevel i1, SortLevel i2) -> if i1 == i2 || ineq && i1 > i2 then OK else Error "comphn, set levels not matching"
    (Type, SortLevel _) | ineq -> OK
    _ -> error "comphn'.2: case should not occur"
  (_, _) -> mpret $ Error "comphn, not equal"

compargs :: CArgList o -> CArgList o -> EE (MyPB o)
compargs args1 args2 =
 mbpcase prioCompareArgList (hnarglist args1) $ \hnargs1 ->
 mbpcase prioCompareArgList (hnarglist args2) $ \hnargs2 ->
 case (hnargs1, hnargs2) of
  (HNALNil, HNALNil) -> mpret OK
  (HNALCons arg1 args1', HNALCons arg2 args2') -> mpret $
   And (Just []) (comp False arg1 arg2) (compargs args1' args2')
  (HNALConPar args1', HNALCons _ args2') -> compargs args1' args2'
  (HNALCons _ args1', HNALConPar args2') -> compargs args1' args2'
  (HNALConPar args1', HNALConPar args2') -> compargs args1' args2'
  (_, _) -> mpret $ Error $ "compargs, not equal"

pickid :: MId -> MId -> MId
pickid mid1@(Id _) _ = mid1
pickid _ mid2 = mid2

-- ---------------------------------

tcSearch :: Ctx o -> CExp o -> MExp o -> EE (MyPB o)
tcSearch ctx typ trm = tcExp False ctx typ trm

