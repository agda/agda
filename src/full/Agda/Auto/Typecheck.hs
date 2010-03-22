

{-# OPTIONS -fglasgow-exts #-}

module Agda.Auto.Typecheck where

import Agda.Utils.Impossible
-- mode: Agda implicit arguments
-- mode: Omitted arguments, used for implicit constructor type arguments
-- mode: A sort can be unknown, used as a hack for Agda's universe polymorphism
import Data.IORef
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax
import Agda.Auto.SearchControl




closify :: MExp o -> CExp o
closify e = TrBr [e] (Clos [] e)

sub :: MExp o -> CExp o -> CExp o
-- sub e (Clos [] x) = Clos [Sub e] x
sub e (TrBr trs (Clos (Skip : as) x)) = TrBr (e : trs) (Clos (Sub (Clos [] e) : as) x)
{-sub e (Clos (Weak n : as) x) = if n == 1 then
                                Clos as x
                               else
                                Clos (Weak (n - 1) : as) x-}
sub _ _ = (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 27))

subi :: MExp o -> ICExp o -> ICExp o
subi e (Clos (Skip : as) x) = Clos (Sub (Clos [] e) : as) x
subi _ _ = (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 31))

weak :: Nat -> CExp o -> CExp o
weak n (TrBr trs e) = TrBr trs (weaki n e)

weaki :: Nat -> Clos a o -> Clos a o
weaki 0 x = x
weaki n (Clos as x) = Clos (Weak n : as) x

weakarglist :: Nat -> ICArgList o -> ICArgList o
weakarglist 0 = id
weakarglist n = f
 where f CALNil = CALNil
       f (CALConcat (Clos cl as) as2) = CALConcat (Clos (Weak n : cl) as) (f as2)
weakelr :: Nat -> Elr o -> Elr o
weakelr 0 elr = elr
weakelr n (Var v) = Var (v + n)
weakelr _ elr@(Const _) = elr


-- ---------------------------------

tcExp :: Bool -> Ctx o -> CExp o -> MExp o -> EE (MyPB o)
tcExp isdep ctx typ@(TrBr typtrs ityp@(Clos _ itypexp)) trm =
  mbpcase prioTypeUnknown Nothing (hnn_checkstep ityp) $ \(hntyp, iotastepdone) ->
  mmpcase (True, prioTypecheck isdep, Just (RIMainInfo (length ctx) hntyp iotastepdone)) trm $ \trm -> case trm of
   App _ okh elr args -> case hntyp of
    HNPi{} | isdep -> mpret $ Error "tcExp, dep terms should be eta-long"
    _ -> do
     (ityp, sc) <- case elr of
              Var v -> -- assuming within scope
               return (weak (v + 1) (snd $ ctx !! v), id)
              Const c -> do
               cdef <- readIORef c
               return (closify (cdtype cdef), \x -> mpret $ And (Just [Term args]) (noiotastep_term c args) x)
     sc $ tcargs okh isdep ctx typ ityp args
   Lam hid (Abs id1 b) -> case hntyp of
    HNPi _ hid2 _ it (Abs id2 ot) | hid == hid2 ->
     tcExp isdep ((pickid id1 id2, t it) : ctx) (t ot) b
    _ -> mpret $ Error "tcExp, type of lam should be fun or pi (and same hid)"
   Pi _ _ _ it (Abs id ot) -> case hntyp of
    HNSort s ->
     mpret $ And (Just [Term ctx, Term it])
      (tcExp True ctx (closify (NotM $ Sort s)) it)
      (tcExp isdep ((id, closify it) : ctx) (closify (NotM $ Sort s)) ot)
    _ -> mpret $ Error "tcExp, type of pi should be set"
   Sort (Set i) -> case hntyp of
    HNSort s2 -> case s2 of
     Set j -> mpret $ if i < j then OK else Error "tcExp, type of set should be larger set"
     UnknownSort -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 89))
     Type -> mpret OK
    _ -> mpret $ Error "tcExp, type of set should be set"
   Sort UnknownSort -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 94))
   Sort Type -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 96))
   AbsurdLambda hid -> case hntyp of
    HNPi _ hid2 _ it _ | hid == hid2 ->
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
 mbcase (hnn t) $ \hnt -> case hnt of
  HNApp _ (Const c) args -> do
   cd <- readIORef c
   case cdcont cd of
    Datatype cons -> mbret $ Just (args, cons) -- ?? check that lenth args corresponds to type of datatype
    _ -> mbret Nothing
  _ -> mbret Nothing
constructorImpossible :: ICArgList o -> ConstRef o -> EE (MyPB o)
constructorImpossible args c = do
 cd <- readIORef c
 mbpcase prioAbsurdLambda Nothing (traversePi (-1) (Clos [] $ cdtype cd)) $ \hnot ->
  case hnot of
   HNApp _ _ args2 -> unequals args args2 (\_ -> mpret $ Error "not unequal") []
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
  case hne2 of
   HNApp _ (Var v2) es2 | v2 < 0 ->
    mbpcase prioAbsurdLambda Nothing (hnarglist es2) $ \hnes2 -> case hnes2 of
     HNALNil ->
      case lookup v2 unifier2 of
       Nothing -> cont ((v2, hne1) : unifier2)
       Just hne2' -> cc hne1 hne2'
     HNALCons{} -> cont unifier2
     HNALConPar{} -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 154))
   _ -> cc hne1 hne2
 where
  cc hne1 hne2 = case (hne1, hne2) of
   (HNApp _ (Const c1) es1, HNApp _ (Const c2) es2) -> do
    cd1 <- readIORef c1
    cd2 <- readIORef c2
    case (cdcont cd1, cdcont cd2) of
     (Constructor, Constructor) ->
      if c1 == c2 then
       unequals es1 es2 cont unifier2
      else
       mpret OK
     _ -> cont unifier2
   _ -> cont unifier2
traversePi :: Int -> ICExp o -> EE (MyMB (HNExp o) o)
traversePi v t =
 mbcase (hnn t) $ \hnt ->
 case hnt of
  HNPi _ _ _ _ (Abs _ ot) -> traversePi (v - 1) (subi (NotM $ App Nothing (NotM OKVal) (Var v) (NotM ALNil)) ot)
  _ -> mbret hnt
tcargs :: OKHandle (RefInfo o) -> Bool -> Ctx o -> CExp o -> CExp o -> MArgList o -> EE (MyPB o)
tcargs okh isdep ctx etyp ityp@(TrBr ityptrs iityp) args = mmpcase (True, prioTypecheckArgList, Nothing) args $ \args' -> case args' of
 ALNil -> mpret $ ConnectHandle okh (comp' True etyp ityp)
 ALCons hid a as ->
  mbpcase prioInferredTypeUnknown (Just RIInferredTypeUnknown) (hnn iityp) $ \hnityp -> case hnityp of
   HNPi _ hid2 possdep it (Abs _ ot) | hid == hid2 -> mpret $
    And (Just ((if possdep then [Term a] else []) ++ [Term ctx, Term ityptrs]))
        (tcExp (isdep || possdep) ctx (t it) a)
        (tcargs okh isdep ctx etyp (sub a (t ot)) as)
   _ -> mpret $ Error "tcargs, inf type should be fun or pi (and same hid)"
 ALConPar _ -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 191))
 where
  t = TrBr ityptrs
-- ---------------------------------
hnn :: ICExp o -> EE (MyMB (HNExp o) o)
hnn e = hnn' e CALNil
hnn_checkstep :: ICExp o -> EE (MyMB (HNExp o, Bool) o)
hnn_checkstep e =
 mbcase (hnb e CALNil) $ \hne ->
  mbcase (iotastep True hne) $ \res -> case res of
   Nothing -> mbret (hne, False)
   Just (e, as) ->
    mbcase (hnn' e as) $ \hne -> mbret (hne, True)
hnn' :: ICExp o -> ICArgList o -> EE (MyMB (HNExp o) o)
hnn' e as =
 mbcase (hnb e as) $ \hne ->
  mbcase (iotastep True hne) $ \res -> case res of
   Nothing -> mbret hne
   Just (e, as) -> hnn' e as
hnb :: ICExp o -> ICArgList o -> EE (MyMB (HNExp o) o)
hnb e as = mbcase (hnc False e as) $ \res -> case res of
            HNDone _ hne -> mbret hne
            HNMeta _ _ -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 220))
data HNRes o = HNDone (Maybe (Metavar (Exp o) (RefInfo o))) (HNExp o)
             | HNMeta (ICExp o) (ICArgList o)
hnc :: Bool -> ICExp o -> ICArgList o -> EE (MyMB (HNRes o) o)
hnc haltmeta = loop
 where
  loop ce@(Clos cl e) cargs =
   (if haltmeta then mmmcase e (mbret $ HNMeta ce cargs) else mmcase e) $
   \ee -> case ee of
    App uid okh elr args ->
     let ncargs = CALConcat (Clos cl args) cargs
     in case elr of
      Var v -> case doclos cl v of
       Left v' -> mbret $ HNDone expmeta (HNApp uid (Var v') ncargs)
       Right f -> loop f ncargs
      Const _ -> mbret $ HNDone expmeta (HNApp uid elr ncargs)
    Lam hid (Abs id b) ->
     mbcase (hnarglist cargs) $ \hncargs -> case hncargs of
      HNALNil -> mbret $ HNDone expmeta (HNLam hid (Abs id (Clos (Skip : cl) b)))
      HNALCons _ arg cargs' -> loop (Clos (Sub arg : cl) b) cargs'
      HNALConPar{} -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 243))
    Pi uid hid possdep it (Abs id ot) -> checkNoArgs cargs $ mbret $ HNDone expmeta (HNPi uid hid possdep (Clos cl it) (Abs id (Clos (Skip : cl) ot)))
    Sort s -> checkNoArgs cargs $ mbret $ HNDone expmeta (HNSort s)
    AbsurdLambda{} -> mbfailed "hnc: encountered absurdlambda"
   where expmeta = case e of {Meta m -> Just m; NotM _ -> Nothing}
  checkNoArgs cargs c =
   mbcase (hnarglist cargs) $ \hncargs -> case hncargs of
    HNALNil -> c
    HNALCons{} -> mbfailed "hnc: there should be no args"
    HNALConPar{} -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 256))
doclos :: [CAction o] -> Nat -> Either Nat (ICExp o)
doclos = f 0
 where
  f ns [] i = Left (ns + i)
  f ns (Weak n : xs) i = f (ns + n) xs i
  f ns (Sub s : _) 0 = Right (weaki ns s)
  f ns (Skip : _) 0 = Left ns
  f ns (Skip : xs) i = f (ns + 1) xs (i - 1)
  f ns (Sub _ : xs) i = f ns xs (i - 1)
hnarglist :: ICArgList o -> EE (MyMB (HNArgList o) o)
hnarglist args =
 case args of
  CALNil -> mbret HNALNil
  CALConcat (Clos cl args) args2 ->
   mmcase args $ \args -> case args of
    ALNil -> hnarglist args2
    ALCons hid arg argsb -> mbret $ HNALCons hid (Clos cl arg) (CALConcat (Clos cl argsb) args2)
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
  HNALConPar{} -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 319))
getAllArgs :: ICArgList o -> EE (MyMB [ICExp o] o)
getAllArgs args =
 mbcase (hnarglist args) $ \hnargs -> case hnargs of
  HNALNil -> mbret []
  HNALCons _ arg args' ->
   mbcase (getAllArgs args') $ \args'' ->
    mbret (arg : args'')
  HNALConPar args2 ->
   mbcase (getAllArgs args2) $ \args3 -> mbret ((throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 331)) : args3)
data PEval o = PENo (ICExp o)
             | PEConApp (ICExp o) (ConstRef o) [PEval o]
iotastep :: Bool -> HNExp o -> EE (MyMB (Maybe (ICExp o, ICArgList o)) o)
iotastep smartcheck e = case e of
 HNApp _ (Const c) args -> do
  cd <- readIORef c
  case cdcont cd of
   Def narg cls _ _ ->
    mbcase (getNArgs narg args) $ \res -> case res of
     Nothing -> mbret Nothing
     Just (pargs, rargs) ->
      mbcase (dorules cls (map PENo pargs)) $ \res -> case res of
       Nothing -> mbret Nothing
       Just rhs -> mbret $ Just (rhs, rargs)
   _ -> mbret Nothing
 _ -> mbret Nothing
 where
 dorules :: [Clause o] -> [PEval o] -> EE (MyMB (Maybe (ICExp o)) o)
 dorules [] _ = mbret Nothing
 dorules (rule:rules') as =
  mbcase (dorule rule as) $ \x -> case x of
   Left (Just as') -> dorules rules' as'
   Left Nothing -> mbret Nothing
   Right rhs -> mbret $ Just rhs
 dorule :: Clause o -> [PEval o] -> EE (MyMB (Either (Maybe [PEval o]) (ICExp o)) o)
 dorule (pats, rhs) as =
  mbcase (dopats pats as) $ \x -> case x of
   Right (_, ss) -> mbret $ Right (Clos (map Sub ss) rhs)
   Left hnas -> mbret $ Left hnas
 dopats :: [Pat o] -> [PEval o] -> EE (MyMB (Either (Maybe [PEval o]) ([PEval o], [ICExp o])) o)
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
 dopats _ _ = (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 378))
 dopat :: Pat o -> PEval o -> EE (MyMB (Either (Maybe (PEval o)) (PEval o, [ICExp o])) o)
 dopat (PatConApp c pas) a =
  case a of
   PENo a ->
    if smartcheck then
     mbcase (meta_not_constructor a) $ \notcon -> if notcon then mbret $ Left Nothing else qq -- to know more often if iota step is possible
    else
     qq
    where
     qq =
      mbcase (hnn a) $ \hna -> case hna of
       HNApp _ (Const c') as ->
        if c == c' then
         mbcase (getAllArgs as) $ \as' ->
          if length as' == length pas then
           mbcase (dopats pas (map PENo as')) $ \x -> case x of
            Right (hnas, ss) -> mbret $ Right (PEConApp a c' hnas, ss)
            Left Nothing -> mbret $ Left Nothing
            Left (Just hnas) -> mbret $ Left $ Just (PEConApp a c' hnas)
          else
           mbfailed "dopat: wrong amount of args"
        else do
         cd <- readIORef c'
         case cdcont cd of
          Constructor -> mbcase (getAllArgs as) $ \as' ->
           mbret $ Left (Just (PEConApp a c' (map PENo as')))
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
 dopat PatVar{} a@(PENo a') = mbret $ Right (a, [a'])
 dopat PatVar{} a@(PEConApp a' _ _) = mbret $ Right (a, [a'])
 dopat PatExp a = mbret $ Right (a, [])
-- -----------------------------
noiotastep :: HNExp o -> EE (MyPB o)
noiotastep hne =
 mbpcase prioNoIota Nothing (iotastep False hne) $ \res -> case res of
  Just _ -> mpret $ Error "iota step possible contrary to assumed"
  Nothing -> mpret OK
noiotastep_term :: ConstRef o -> MArgList o -> EE (MyPB o)
noiotastep_term c args = f (HNApp Nothing (Const c) (CALConcat (Clos [] args) CALNil))
 where
  f hne@(HNApp _ (Const c) _) = do
   cd <- readIORef c
   let isshorthand =
        case cdcont cd of
         Def _ [(pats, _)] _ _ -> all (\pat -> case pat of {PatConApp{} -> False; _ -> True}) pats
         _ -> False
   if isshorthand then
     mpret OK
    else
     noiotastep hne
  f _ = (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 444))
data CMode o = CMRigid (Maybe (Metavar (Exp o) (RefInfo o))) (HNExp o)
             | forall b . Refinable b (RefInfo o) => CMFlex (MM b (RefInfo o)) (CMFlex o)
data CMFlex o = CMFFlex (ICExp o) (ICArgList o)
              | CMFSemi (Maybe (Metavar (Exp o) (RefInfo o))) (HNExp o)
              | CMFBlocked (Maybe (Metavar (Exp o) (RefInfo o))) (HNExp o)
comp' :: forall o . Bool -> CExp o -> CExp o -> EE (MyPB o)
comp' ineq lhs@(TrBr trs1 e1) rhs@(TrBr trs2 e2) = comp ineq e1 e2 
 where
  comp :: Bool -> ICExp o -> ICExp o -> EE (MyPB o)
  comp ineq e1 e2 = f True e1 CALNil $ \res1 -> f True e2 CALNil $ \res2 -> g res1 res2
   where
    f semifok e as cont =
     mbpcase prioCompBeta Nothing (hnc True e as) $ \res ->
      case res of
       HNDone mexpmeta hne -> fhn semifok mexpmeta hne cont
       HNMeta ce@(Clos _ m) cargs -> cont (CMFlex m (CMFFlex ce cargs))
    fhn semifok mexpmeta hne cont =
     mmbpcase (iotastep True hne)
      (\m -> do
        sf <- return False {- semiflex hne -}
        if semifok && sf then
          cont (CMFlex m (CMFSemi mexpmeta hne))
         else
          cont (CMFlex m (CMFBlocked mexpmeta hne))
      )
      (\res -> case res of
        Nothing -> cont (CMRigid mexpmeta hne)
        Just (e, as) -> f semifok e as cont
      )
    g res1 res2 =
     case (res1, res2) of
      (CMRigid mexpmeta1 hne1, CMRigid mexpmeta2 hne2) -> comphn ineq mexpmeta1 hne1 mexpmeta2 hne2
      (CMFlex m1 (CMFBlocked mexpmeta1 hne1), _) -> mstp False mexpmeta1 hne1 $ \res1 -> g res1 res2
      (_, CMFlex m2 (CMFBlocked mexpmeta2 hne2)) -> mstp False mexpmeta2 hne2 $ \res2 -> g res1 res2
      (CMRigid mexpmeta1 hne1, CMFlex _ fl2) -> unif True mexpmeta1 hne1 fl2
      (CMFlex _ fl1, CMRigid mexpmeta2 hne2) -> unif False mexpmeta2 hne2 fl1
      (CMFlex m1 fl1, CMFlex m2 fl2) -> doubleblock m1 m2 $ fcm fl1 $ \res1 -> fcm fl2 $ \res2 -> g res1 res2
    fcm (CMFFlex ce cargs) = f True ce cargs
    fcm (CMFSemi mexpmeta hne) = fhn True mexpmeta hne
    fcm (CMFBlocked _ hne) = (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 490)) -- not used. if so should be: fhn False hne
    mstp semif mexpmeta hne cont =
     mpret $ Or prioCompChoice
      (mpret $ And (Just [Term lhs, Term rhs])
       (noiotastep hne)
       (cont (CMRigid mexpmeta hne))
      )
      (stp semif hne cont)
    stp semif hne cont =
     mbpcase prioCompIota (Just $ RIIotaStep semif) (iotastep True hne) $ \res -> case res of
      Nothing -> mpret $ Error "no iota step possible, contrary to assumed"
      Just (e, as) -> f semif e as cont
    unif oppis1 oppmexpmeta opphne res =
     let iter res = if oppis1 then
                     g (CMRigid oppmexpmeta opphne) res
                    else
                     g res (CMRigid oppmexpmeta opphne)
     in case res of
      CMFFlex ce cargs -> do
       poss <- iotapossmeta ce cargs
       maybeor poss prioCompChoice
        (loop ce cargs)
        (mbpcase prioCompBeta (Just $ RIIotaStep False) (hnb ce cargs) $ \hne ->
          -- RIIotaStep here on beta-norm to make cost high when guessing elim const in type par
         stp False hne iter
        )
       where
        loop ce@(Clos cl m) cargs =
         mmpcase (False, prioCompUnif, Just (RIUnifInfo cl opphne)) m $ \_ ->
         mbpcase prioCompBeta Nothing (hnc True ce cargs) $ \res -> case res of
          HNDone mexpmeta hne ->
           mpret $ And (Just [Term lhs, Term rhs])
            (noiotastep hne)
            (iter (CMRigid mexpmeta hne))
          HNMeta ce cargs -> loop ce cargs
      CMFSemi _ hne ->
       (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 526)) -- CMFSemi disabled, if used should be: stp True hne iter
      CMFBlocked{} -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 527))
    comphn :: Bool -> Maybe (Metavar (Exp o) (RefInfo o)) -> HNExp o -> Maybe (Metavar (Exp o) (RefInfo o)) -> HNExp o -> EE (MyPB o)
    comphn ineq mexpmeta1 hne1 mexpmeta2 hne2 =
     case (hne1, hne2) of
      (HNApp _ elr1 args1, HNApp _ elr2 args2) ->
       let ce = case (elr1, elr2) of
                 (Var v1, Var v2) -> if v1 == v2 then Nothing else Just "comphn, elr, vars not equal"
                 (Const c1, Const c2) -> if c1 == c2 then Nothing else Just "comphn, elr, consts not equal"
                 (_, _) -> Just "comphn, elrs not equal"
       in case ce of
            Nothing -> compargs args1 args2
            Just msg -> mpret $ Error msg
      (HNApp uid1 (Const c1) _, _) -> case mexpmeta2 of
       Nothing -> mpret $ Error "comphn, not equal (2)"
       Just m2 -> mpret $ AddExtraRef "comphn: not equal, adding extra ref" m2 (extraref m2 uid1 c1)
      (_, HNApp uid2 (Const c2) _) -> case mexpmeta1 of
       Nothing -> mpret $ Error "comphn, not equal (3)"
       Just m1 -> mpret $ AddExtraRef "comphn: not equal, adding extra ref" m1 (extraref m1 uid2 c2)
      (HNLam hid1 (Abs id1 b1), HNLam hid2 (Abs id2 b2)) {-| hid1 == hid2-} -> comp False b1 b2
      (HNLam _ (Abs _ b1), HNApp uid2 elr2 args2) ->
       f True b1 CALNil $ \res1 -> g res1
        (CMRigid mexpmeta2 (HNApp uid2 (weakelr 1 elr2) (addtrailingargs (Clos [] $ NotM $ ALCons NotHidden{- arbitrary -} (NotM $ App Nothing (NotM OKVal) (Var 0) (NotM ALNil)) (NotM ALNil)) (weakarglist 1 args2))))
      (HNApp uid1 elr1 args1, HNLam _ (Abs _ b2)) ->
       f True b2 CALNil $ \res2 -> g
        (CMRigid mexpmeta1 (HNApp uid1 (weakelr 1 elr1) (addtrailingargs (Clos [] $ NotM $ ALCons NotHidden{- arbitrary -} (NotM $ App Nothing (NotM OKVal) (Var 0) (NotM ALNil)) (NotM ALNil)) (weakarglist 1 args1))))
        res2
      (HNPi _ hid1 _ it1 (Abs id1 ot1), HNPi _ hid2 _ it2 (Abs id2 ot2)) {-| hid1 == hid2-} -> mpret $
       And (Just [Term trs1, Term trs2]) (comp False it1 it2) (comp ineq ot1 ot2)
      (HNSort s1, HNSort s2) -> mpret $
       case (s1, s2) of
        (Set i1, Set i2) -> if i1 == i2 || ineq && i1 > i2 then OK else Error "comphn, set levels not matching"
        (Set _, UnknownSort) -> OK
        (UnknownSort, Set _) -> OK
        (UnknownSort, UnknownSort) -> OK
        (Type, Set _) | ineq -> OK
        (Type, UnknownSort) | ineq -> OK
        _ -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 572))
      (_, _) -> mpret $ Error "comphn, not equal"
    compargs :: ICArgList o -> ICArgList o -> EE (MyPB o)
    compargs args1 args2 =
     mbpcase prioCompareArgList Nothing (hnarglist args1) $ \hnargs1 ->
     mbpcase prioCompareArgList Nothing (hnarglist args2) $ \hnargs2 ->
     case (hnargs1, hnargs2) of
      (HNALNil, HNALNil) -> mpret OK
      (HNALCons hid1 arg1 args1b, HNALCons hid2 arg2 args2b) {-| hid1 == hid2-} -> mpret $
       And (Just [Term trs1, Term trs2]) (comp False arg1 arg2) (compargs args1b args2b)
      (HNALConPar args1b, HNALCons _ _ args2b) -> compargs args1b args2b
      (HNALCons _ _ args1b, HNALConPar args2b) -> compargs args1b args2b
      (HNALConPar args1', HNALConPar args2') -> compargs args1' args2'
      (_, _) -> mpret $ Error $ "comphnargs, not equal"
-- ---------------------------------
checkeliminand :: MExp o -> EE (MyPB o)
checkeliminand = f [] []
 where
  f uids used e =
   mmpcase (False, prioNo, Just (RIUsedVars uids used)) e $ \e -> case e of
    App uid _ (Var v) args -> fs (adduid uid uids) (v : used) args
    App uid _ (Const c) args -> do
     cd <- readIORef c
     case cdcont cd of
      Def _ _ (Just i) _ -> mpret $ Sidecondition (fs (adduid uid uids) used args) (g i args)
       where
        g i as = mmpcase (False, prioNo, Nothing) as $ \as -> case as of
                  ALNil -> mpret OK
                  ALCons _ a as -> case i of
                   0 -> mmpcase (False, prioNo, Just RINotConstructor) a $ \_ ->
                         mpret OK
                   _ -> g (i - 1) as
                  ALConPar as -> case i of
                   0 -> (throwImpossible (Impossible ("agsy: " ++ "../agsy/Agda/Auto/Typecheck.hs") 645))
                   _ -> g (i - 1) as
      _ -> fs (adduid uid uids) used args
    Lam _ (Abs _ e) -> f uids (w used) e
    Pi uid _ _ e1 (Abs _ e2) -> mpret $ Sidecondition (f (adduid uid uids) used e1) (f (adduid uid uids) (w used) e2)
    Sort _ -> mpret OK
    AbsurdLambda{} -> mpret OK
  fs uids used as =
   mmpcase (False, prioNo, Nothing) as $ \as -> case as of
    ALNil -> mpret OK
    ALCons _ a as -> mpret $ Sidecondition (f uids used a) (fs uids used as)
    ALConPar as -> fs uids used as
  w = map (+ 1)
  adduid (Just uid) uids = uid : uids
  adduid Nothing uids = uids
-- ---------------------------------
maybeor True prio mainalt alt = mpret $ Or prio mainalt alt
maybeor False _ mainalt _ = mainalt
iotapossmeta :: ICExp o -> ICArgList o -> EE Bool
iotapossmeta ce@(Clos cl _) cargs = do
 xs <- mapM ncaction cl
 y <- nccargs cargs
 return $ not (all id xs && y)
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
  ncargs cl (ALConPar args) = ncmargs cl args
  nonconstructor :: ICExp o -> EE Bool
  nonconstructor ce = do
   res <- hnn ce
   case res of
    NotB hne -> case hne of
     HNApp _ (Const c) _ -> do
      cd <- readIORef c
      case cdcont cd of
       Constructor -> return False
       _ -> return True
     _ -> return True
    Blocked m _ -> return False -- not necessary to do check here because already done by hnn (!! if it's known that m stands for an eliminator then it cannot be constructor so True instead)
    Failed _ -> return False
meta_not_constructor :: ICExp o -> EE (MB Bool (RefInfo o))
meta_not_constructor a =
 mbcase (hnc True a CALNil) $ \res -> case res of
  HNMeta ce _ -> do
    let (Clos _ (Meta m)) = ce
    infos <- extractblkinfos m
    mbret $ any (\info -> case info of {RINotConstructor -> True; _ -> False}) infos
  HNDone{} -> mbret False
-- ---------------------------------
pickid :: MId -> MId -> MId
pickid mid1@(Id _) _ = mid1
pickid _ mid2 = mid2
-- ---------------------------------
tcSearch :: Bool -> Ctx o -> CExp o -> MExp o -> EE (MyPB o)
tcSearch isdep ctx typ trm = mpret $ Sidecondition (checkeliminand trm)
                              (tcExp isdep ctx typ trm)
-- ----------------------------
-- ---------------------------------
