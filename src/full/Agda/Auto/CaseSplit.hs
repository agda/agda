{-# LANGUAGE CPP #-}

module Agda.Auto.CaseSplit where

import Data.IORef
import Data.Tuple (swap)
import Data.List (findIndex, union)
import qualified Data.Set    as Set
import qualified Data.IntMap as IntMap

import Agda.Syntax.Common (Hiding(..))
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax

import Agda.Auto.SearchControl
import Agda.Auto.Typecheck

#include "undefined.h"
import Agda.Utils.Impossible

abspatvarname :: String
abspatvarname = "\0absurdPattern"

costCaseSplitVeryHigh, costCaseSplitHigh, costCaseSplitLow, costAddVarDepth
  :: Cost
costCaseSplitVeryHigh = 10000
costCaseSplitHigh     = 5000
costCaseSplitLow      = 2000
costAddVarDepth       = 1000

data HI a = HI Hiding a

drophid :: [HI a] -> [a]
drophid = map (\(HI _ x) -> x)

type CSPat o = HI (CSPatI o)
type CSCtx o = [HI (MId, MExp o)]

data CSPatI o = CSPatConApp (ConstRef o) [CSPat o]
              | CSPatVar Nat
              | CSPatExp (MExp o)
              | CSWith (MExp o) -- always an App
              | CSAbsurd

              | CSOmittedArg
type Sol o = [(CSCtx o, [CSPat o], Maybe (MExp o))]

caseSplitSearch ::
  forall o . IORef Int -> Int -> [ConstRef o] ->
  Maybe (EqReasoningConsts o) -> Int -> Cost -> ConstRef o ->
  CSCtx o -> MExp o -> [CSPat o] -> IO [Sol o]
caseSplitSearch ticks nsolwanted chints meqr depthinterval depth recdef ctx tt pats = do
 let branchsearch :: Cost -> CSCtx o -> MExp o ->
                     ([Nat], Nat, [Nat]) -> IO (Maybe (MExp o))
     branchsearch depth ctx tt termcheckenv = do

      nsol <- newIORef 1
      m <- initMeta
      sol <- newIORef Nothing
      let trm = Meta m
          hsol = do trm' <- expandMetas trm
                    writeIORef sol (Just trm')
          initcon = mpret
                  $ Sidecondition
                    (localTerminationSidecond termcheckenv recdef trm)
                  $ (case meqr of
                        Nothing  -> id
                        Just eqr -> mpret . Sidecondition (calcEqRState eqr trm)
                     ) $ tcSearch False (map (fmap closify) (drophid ctx))
                         (closify tt) trm
      recdefd <- readIORef recdef
      let env = RIEnv { rieHints = (recdef, HMRecCall) : map (, HMNormal) chints
                      , rieDefFreeVars = cddeffreevars recdefd
                      , rieEqReasoningConsts = meqr
                      }
      depreached <- topSearch ticks nsol hsol env initcon depth (depth + 1)
      rsol <- readIORef sol
      return rsol
     ctx' = ff 1 ctx
     ff _ [] = []
     ff n (HI hid (id, t) : ctx) = HI hid (id, lift n t) : ff (n + 1) ctx
 caseSplitSearch' branchsearch depthinterval depth recdef ctx' tt pats

caseSplitSearch' :: forall o .
  (Cost -> CSCtx o -> MExp o -> ([Nat], Nat, [Nat]) -> IO (Maybe (MExp o))) ->
  Int -> Cost -> ConstRef o -> CSCtx o -> MExp o -> [CSPat o] -> IO [Sol o]
caseSplitSearch' branchsearch depthinterval depth recdef ctx tt pats = do
  recdefd <- readIORef recdef
  sols <- rc depth (cddeffreevars recdefd) ctx tt pats
  return sols
 where
  rc :: Cost -> Int -> CSCtx o -> MExp o -> [CSPat o] -> IO [Sol o]
  rc depth _ _ _ _ | depth < 0 = return []
  rc depth nscrutavoid ctx tt pats = do

    mblkvar <- getblks tt


    fork
     mblkvar
   where
   fork :: [Nat] -> IO [Sol o]
   fork mblkvar = do
    sols1 <- dobody
    case sols1 of
     (_:_) -> return sols1
     [] -> do
      let r [] = return []
          r (v:vs) = do
           sols2 <- splitvar mblkvar v
           case sols2 of
            (_:_) -> return sols2
            [] -> r vs
      r [nv - x | x <- [0..nv]] -- [0..length ctx - 1 - nscrutavoid]
    where nv = length ctx - 1
   dobody :: IO [Sol o]
   dobody = do
    case findperm (map snd (drophid ctx)) of
     Just perm -> do
      let (ctx', tt', pats') = applyperm perm ctx tt pats
      res <- branchsearch depth ctx' tt' (localTerminationEnv pats')
      return $ case res of
       Just trm -> [[(ctx', pats', Just trm)]]
       Nothing -> []
     Nothing -> __IMPOSSIBLE__ -- no permutation found
   splitvar :: [Nat] -> Nat -> IO [Sol o]
   splitvar mblkvar scrut = do
    let scruttype = infertypevar ctx scrut
    case rm scruttype of
     App _ _ (Const c) _ -> do
      cd <- readIORef c
      case cdcont cd of
       Datatype cons _ -> do
         sols <- dobranches cons
         return $ map (\sol -> case sol of
          [] ->
           case findperm (map snd (drophid ctx)) of
            Just perm ->
             let HI scrhid(_, scrt) = ctx !! scrut
                 ctx1 = take scrut ctx ++ (HI scrhid (Id abspatvarname, scrt)) : drop (scrut + 1) ctx
                 (ctx', _, pats') = applyperm perm ctx1 tt ({-map (replacep scrut 1 CSAbsurd __IMPOSSIBLE__) -}pats)
             in [(ctx', pats', Nothing)]
            Nothing -> __IMPOSSIBLE__ -- no permutation found
          _ -> sol
          ) sols
        where
         dobranches :: [ConstRef o] -> IO [Sol o]
         dobranches [] = return [[]]
         dobranches (con : cons) = do
          cond <- readIORef con
          let ff t = case rm t of
                        Pi _ h _ it (Abs id ot) ->
                         let (xs, inft) = ff ot
                         in (((h, scrut + length xs), id, lift (scrut + length xs + 1) it) : xs, inft)
                        _ -> ([], lift scrut t)
              (newvars, inftype) = ff (cdtype cond)
              constrapp = NotM $ App Nothing (NotM OKVal) (Const con) (foldl (\xs ((h, v), _, _) -> NotM $ ALCons h (NotM $ App Nothing (NotM OKVal) (Var v) (NotM ALNil)) xs) (NotM ALNil) (reverse newvars))
              pconstrapp = CSPatConApp con (map (\((hid, v), _, _) -> HI hid (CSPatVar v)) newvars)
              thesub = replace scrut (length newvars) constrapp
              Id newvarprefix = fst $ (drophid ctx) !! scrut
              ctx1 = map (\(HI hid (id, t)) -> HI hid (id, thesub t)) (take scrut ctx) ++
                     reverse (map (\(((hid, _), id, t), i) ->
                       HI hid (Id (case id of {NoId -> newvarprefix{- ++ show i-}; Id id -> id}), t)
                      ) (zip newvars [0..])) ++
                     map (\(HI hid (id, t)) -> HI hid (id, thesub t)) (drop (scrut + 1) ctx)
              tt' = thesub tt
              pats' = map (replacep scrut (length newvars) pconstrapp constrapp) pats
              scruttype' = thesub scruttype  -- scruttype shouldn't really refer to scrutvar so lift is enough, but what if circular ref has been created and this is not detected until case split is done
          case unifyexp inftype scruttype' of
           Nothing -> do
            res <- notequal scrut (length newvars) scruttype' inftype
            if res then -- branch absurd
              dobranches cons
             else -- branch dont know
              return []
           Just unif ->
            do
             let (ctx2, tt2, pats2) = removevar ctx1 tt' pats' unif
                 --cost = if elem scrut mblkvar then costCaseSplit - (costCaseSplit - costCaseSplitFollow) `div` (length mblkvar) else costCaseSplit
                 cost = if null mblkvar then
                         if scrut < length ctx - nscrutavoid && nothid
                         then costCaseSplitLow + costAddVarDepth
                              * Cost (depthofvar scrut pats)
                         else costCaseSplitVeryHigh
                        else
                         if elem scrut mblkvar then costCaseSplitLow else (if scrut < length ctx - nscrutavoid && nothid then costCaseSplitHigh else costCaseSplitVeryHigh)

                 nothid = let HI hid _ = ctx !! scrut
                          in case hid of {Hidden -> False; Instance -> False; NotHidden -> True}


             sols <- rc (depth - cost) (length ctx - 1 - scrut) ctx2 tt2 pats2
             case sols of
              [] -> return []
              _ -> do
               sols2 <- dobranches cons
               return $ concat (map (\sol -> map (\sol2 -> sol ++ sol2) sols2) sols)
       _ -> return [] -- split failed "scrut type is not datatype"
     _ -> return [] -- split failed "scrut type is not datatype"

infertypevar :: CSCtx o -> Nat -> MExp o
infertypevar ctx v = snd $ (drophid ctx) !! v

replace :: Nat -> Nat -> MExp o -> MExp o -> MExp o
replace sv nnew re = r 0
 where
  r n e =
   case rm e of
         App uid ok elr@(Var v) args ->
          if v >= n then
           if v - n == sv then
            betareduce (lift n re) (rs n args)
           else
            if v - n > sv then
             NotM $ App uid ok (Var (v + nnew - 1)) (rs n args)
            else
             NotM $ App uid ok elr (rs n args)
          else
           NotM $ App uid ok elr (rs n args)
         App uid ok elr@(Const _) args ->
          NotM $ App uid ok elr (rs n args)
         Lam hid (Abs mid e) -> NotM $ Lam hid (Abs mid (r (n + 1) e))
         Pi uid hid possdep it (Abs mid ot) -> NotM $ Pi uid hid possdep (r n it) (Abs mid (r (n + 1) ot))
         Sort{} -> e

         AbsurdLambda{} -> e


  rs n es =
   case rm es of
    ALNil -> NotM $ ALNil
    ALCons hid a as -> NotM $ ALCons hid (r n a) (rs n as)

    ALProj{} -> __IMPOSSIBLE__


    ALConPar as -> NotM $ ALConPar (rs n as)


betareduce :: MExp o -> MArgList o -> MExp o
betareduce e args = case rm args of
 ALNil -> e
 ALCons _ a rargs -> case rm e of
  App uid ok elr eargs -> NotM $ App uid ok elr (concatargs eargs args)
  Lam _ (Abs _ b) -> betareduce (replace 0 0 a b) rargs
  _ -> __IMPOSSIBLE__ -- not type correct if this happens

 ALProj{} -> __IMPOSSIBLE__

 ALConPar as -> __IMPOSSIBLE__

concatargs :: MM (ArgList o) (RefInfo o) -> MArgList o -> MArgList o
concatargs xs ys = case rm xs of
  ALNil -> ys

  ALCons hid x xs -> NotM $ ALCons hid x (concatargs xs ys)

  ALProj{} -> __IMPOSSIBLE__

  ALConPar as -> NotM $ ALConPar (concatargs xs ys)

replacep :: Nat -> Nat -> CSPatI o -> MExp o -> CSPat o -> CSPat o
replacep sv nnew rp re = r
 where
  r (HI hid (CSPatConApp c ps)) = HI hid (CSPatConApp c (map r ps))
  r (HI hid (CSPatVar v)) = if v == sv then
                    HI hid rp
                   else
                    if v > sv then
                     HI hid (CSPatVar (v + nnew - 1))
                    else
                     HI hid (CSPatVar v)
  r (HI hid (CSPatExp e)) = HI hid (CSPatExp $ replace sv nnew re e)

  r p@(HI _ CSOmittedArg) = p

  r _ = __IMPOSSIBLE__ -- other constructors dont appear in indata Pats

unifyexp :: MExp o -> MExp o -> Maybe [(Nat, MExp o)]
unifyexp e1 e2 = r e1 e2 (\unif -> Just unif) []
 where
  r e1 e2 cont unif = case (rm e1, rm e2) of
   (App _ _ elr1 args1, App _ _ elr2 args2) | elr1 == elr2 -> rs args1 args2 cont unif
   (Lam hid1 (Abs _ b1), Lam hid2 (Abs _ b2)) | hid1 == hid2 -> r b1 b2 cont unif
   (Pi _ hid1 _ it1 (Abs _ ot1), Pi _ hid2 _ it2 (Abs _ ot2)) | hid1 == hid2 -> r it1 it2 (r ot1 ot2 cont) unif
   (Sort _, Sort _) -> cont unif -- a bit sloppy
   (App _ _ (Var v) (NotM ALNil), App _ _ (Var u) (NotM ALNil))
     | v == u -> cont unif
   (App _ _ (Var v) (NotM ALNil), _)
     | elem v (freevars e2) -> Nothing -- Occurs check
   (_, App _ _ (Var v) (NotM ALNil))
     | elem v (freevars e1) -> Nothing -- Occurs check
   (App _ _ (Var v) (NotM ALNil), _) ->
    case lookup v unif of
     Nothing -> cont ((v, e2) : unif)
     Just e1' -> r e1' e2 cont unif
   (_, App _ _ (Var v) (NotM ALNil)) ->
    case lookup v unif of
     Nothing -> cont ((v, e1) : unif)
     Just e2' -> r e1 e2' cont unif
   _ -> Nothing
  rs args1 args2 cont unif = case (rm args1, rm args2) of
   (ALNil, ALNil) -> cont unif
   (ALCons hid1 a1 as1, ALCons hid2 a2 as2) | hid1 == hid2 -> r a1 a2 (rs as1 as2 cont) unif
   (ALConPar as1, ALCons _ _ as2) -> rs as1 as2 cont unif
   (ALCons _ _ as1, ALConPar as2) -> rs as1 as2 cont unif
   (ALConPar as1, ALConPar as2) -> rs as1 as2 cont unif
   _ -> Nothing

lift :: Nat -> MExp o -> MExp o
lift 0 = id
lift n = r 0
 where
  r j e =
   case rm e of
         App uid ok elr args -> case elr of
          Var v | v >= j -> NotM $ App uid ok (Var (v + n)) (rs j args)
          _ -> NotM $ App uid ok elr (rs j args)
         Lam hid (Abs mid e) -> NotM $ Lam hid (Abs mid (r (j + 1) e))
         Pi uid hid possdep it (Abs mid ot) -> NotM $ Pi uid hid possdep (r j it) (Abs mid (r (j + 1) ot))
         Sort{} -> e

         AbsurdLambda{} -> e


  rs j es =
   case rm es of
    ALNil -> NotM ALNil
    ALCons hid a as -> NotM $ ALCons hid (r j a) (rs j as)

    ALProj{} -> __IMPOSSIBLE__


    ALConPar as -> NotM $ ALConPar (rs j as)


removevar :: CSCtx o -> MExp o -> [CSPat o] -> [(Nat, MExp o)] -> (CSCtx o, MExp o, [CSPat o])
removevar ctx tt pats [] = (ctx, tt, pats)
removevar ctx tt pats ((v, e) : unif) =
 let
  e2 = replace v 0 (__IMPOSSIBLE__ {- occurs check failed -}) e
  thesub = replace v 0 e2
  ctx1 = map (\(HI hid (id, t)) -> HI hid (id, thesub t)) (take v ctx) ++
         map (\(HI hid (id, t)) -> HI hid (id, thesub t)) (drop (v + 1) ctx)
  tt' = thesub tt
  pats' = map (replacep v 0 (CSPatExp e2) e2) pats
  unif' = map (\(uv, ue) -> (if uv > v then uv - 1 else uv, thesub ue)) unif
 in
  removevar ctx1 tt' pats' unif'

notequal :: Nat -> Nat -> MExp o -> MExp o -> IO Bool
notequal firstnew nnew e1 e2 =
  case (rm e1, rm e2) of
   (App _ _ _ es1, App _ _ _ es2) -> rs es1 es2 (\_ -> return False) []
   _ -> __IMPOSSIBLE__
 where
  rs :: MArgList o -> MArgList o -> ([(Nat, MExp o)] -> IO Bool) -> [(Nat, MExp o)] -> IO Bool
  rs es1 es2 cont unifier2 =
   case (rm es1, rm es2) of
    (ALCons _ e1 es1, ALCons _ e2 es2) -> r e1 e2 (rs es1 es2 cont) unifier2

    (ALConPar es1, ALConPar es2) -> rs es1 es2 cont unifier2

    _ -> cont unifier2

  r :: MExp o -> MExp o -> ([(Nat, MExp o)] -> IO Bool) -> [(Nat, MExp o)] -> IO Bool
  r e1 e2 cont unifier2 = case rm e2 of
   App _ _ (Var v2) es2 | firstnew <= v2 && v2 < firstnew + nnew ->
    case rm es2 of
     ALNil ->
      case lookup v2 unifier2 of
       Nothing -> cont ((v2, e1) : unifier2)
       Just e2' -> cc e1 e2'
     ALCons{} -> cont unifier2

     ALProj{} -> __IMPOSSIBLE__


     ALConPar{} -> __IMPOSSIBLE__

   _ -> cc e1 e2
   where
   cc e1 e2 = case (rm e1, rm e2) of
    (App _ _ (Const c1) es1, App _ _ (Const c2) es2) -> do
     cd1 <- readIORef c1
     cd2 <- readIORef c2
     case (cdcont cd1, cdcont cd2) of
      (Constructor{}, Constructor{}) ->
       if c1 == c2 then
        rs es1 es2 cont unifier2
       else
        return True
      _ -> cont unifier2
    _ -> cont unifier2

findperm :: [MExp o] -> Maybe [Nat]
findperm ts =
 let
  frees = map freevars ts
  m = IntMap.fromList $
      map (\i -> (i, length (filter (elem i) frees)))
          [0..length ts - 1]
  r _ perm 0 = Just $ reverse perm
  r m perm n =
   case lookup 0 (map swap (IntMap.toList m)) of
    Nothing -> Nothing
    Just i -> r (foldl (flip $ IntMap.adjust (subtract 1))
                       (IntMap.insert i (-1) m)
                       (frees !! i))
                 (i : perm) (n - 1)
 in r m [] (length ts)


freevars :: MExp o -> [Nat]
freevars = Set.toList . freeVars

applyperm :: [Nat] -> CSCtx o -> MExp o -> [CSPat o] ->
             (CSCtx o, MExp o, [CSPat o])
applyperm perm ctx tt pats =
 let ctx1 = map (\(HI hid (id, t)) -> HI hid (id, rename (ren perm) t)) ctx
     ctx2 = map (\i -> ctx1 !! i) perm
     ctx3 = seqctx ctx2
     tt' = rename (ren perm) tt
     pats' = map (rename (ren perm)) pats
 in (ctx3, tt', pats')

ren :: [Nat] -> Nat -> Int
ren n i = let Just j = findIndex (== i) n in j

instance Renaming t => Renaming (HI t) where
  renameOffset j ren (HI hid t) = HI hid $ renameOffset j ren t

instance Renaming (CSPatI o) where
  renameOffset j ren e = case e of
    CSPatConApp c pats -> CSPatConApp c $ map (renameOffset j ren) pats
    CSPatVar i         -> CSPatVar $ j + ren i
    CSPatExp e         -> CSPatExp $ renameOffset j ren e
    CSOmittedArg       -> e
    _                  -> __IMPOSSIBLE__

seqctx :: CSCtx o -> CSCtx o
seqctx = r (-1)
 where
  r _ [] = []
  r n (HI hid (id, t) : ctx) = HI hid (id, lift n t) : r (n - 1) ctx
-- --------------------

depthofvar :: Nat -> [CSPat o] -> Nat
depthofvar v pats =
 let [depth] = concatMap (f 0) (drophid pats)
     f d (CSPatConApp _ pats) = concatMap (f (d + 1)) (drophid pats)
     f d (CSPatVar v') = if v == v' then [d] else []
     f _ _ = []
 in depth

-- --------------------

localTerminationEnv :: [CSPat o] -> ([Nat], Nat, [Nat])
localTerminationEnv pats =
 let g _ [] = ([], 0, [])
     g i (hp@(HI _ p) : ps) = case p of
      CSPatConApp{} ->
       let (size, vars) = h hp
           (is, size', vars') = g (i + 1) ps
       in (i : is, size + size', vars ++ vars')
      _ -> g (i + 1) ps
     h (HI _ p) = case p of
      CSPatConApp c ps ->
       let (size, vars) = hs ps
       in (size + 1, vars)
      CSPatVar n -> (0, [n])
      CSPatExp e -> he e
      _ -> (0, [])
     hs [] = (0, [])
     hs (p : ps) =
      let (size, vars) = h p
          (size', vars') = hs ps
      in (size + size', vars ++ vars')
     he e = case rm e of
      App _ _ (Var v) _ -> (0, [v])
      App _ _ (Const _) args ->
       let (size, vars) = hes args
       in (size + 1, vars)
      _ -> (0, [])
     hes as = case rm as of
      ALNil -> (0, [])
      ALCons _ a as ->
       let (size, vars) = he a
           (size', vars') = hes as
       in (size + size', vars ++ vars')

      ALProj{} -> __IMPOSSIBLE__


      ALConPar as -> hes as

 in g 0 pats


localTerminationSidecond :: ([Nat], Nat, [Nat]) -> ConstRef o -> MExp o -> EE (MyPB o)
localTerminationSidecond (is, size, vars) reccallc b =
  ok b
 where
     ok e = mmpcase (False, prioNo, Nothing) e $ \e -> case e of
      App _ _ elr args -> mpret $ Sidecondition
       (oks args)
       (case elr of
          Const c | c == reccallc -> if size == 0 then mpret (Error "localTerminationSidecond: no size to decrement") else okcall 0 size vars args
          _ -> mpret OK
       )
      Lam _ (Abs _ e) -> ok e
      Pi _ _ _ it (Abs _ ot) -> mpret $ Sidecondition
       (ok it)
       (ok ot)
      Sort{} -> mpret OK

      AbsurdLambda{} -> mpret OK


     oks as = mmpcase (False, prioNo, Nothing) as $ \as -> case as of
      ALNil -> mpret OK
      ALCons _ a as -> mpret $ Sidecondition
       (ok a)
       (oks as)

      ALProj eas _ _ as -> mpret $ Sidecondition (oks eas) (oks as)


      ALConPar as -> oks as

     okcall i size vars as = mmpcase (False, prioNo, Nothing) as $ \as -> case as of
      ALNil -> mpret OK
      ALCons _ a as | elem i is ->
       mbpcase prioNo Nothing (he size vars a) $ \x -> case x of
        Nothing -> mpret $ Error "localTerminationSidecond: reccall not ok"
        Just (size', vars') -> okcall (i + 1) size' vars' as
      ALCons _ a as -> okcall (i + 1) size vars as

      ALProj{} -> mpret OK


      ALConPar as -> __IMPOSSIBLE__

     he size vars e = mmcase e $ \e -> case e of
      App _ _ (Var v) _ ->
       case remove v vars of
        Nothing -> mbret Nothing
        Just vars' -> mbret $ Just (size, vars')
      App _ _ (Const c) args -> do
       cd <- readIORef c
       case cdcont cd of
        Constructor{} ->
         if size == 1 then
          mbret Nothing
         else
          hes (size - 1) vars args
        _ -> mbret Nothing
      _ -> mbret Nothing
     hes size vars as = mmcase as $ \as -> case as of
      ALNil -> mbret $ Just (size, vars)
      ALCons _ a as ->
       mbcase (he size vars a) $ \x -> case x of
        Nothing -> mbret Nothing
        Just (size', vars') -> hes size' vars' as

      ALProj{} -> __IMPOSSIBLE__


      ALConPar as -> __IMPOSSIBLE__

     remove _ [] = Nothing
     remove x (y : ys) | x == y = Just ys
     remove x (y : ys) = case remove x ys of {Nothing -> Nothing; Just ys' -> Just (y : ys')}

-- ---------------------------


getblks :: MExp o -> IO [Nat]
getblks tt = do
 NotB (hntt, blks) <- hnn_blks (Clos [] tt)
 case f blks of
  Just v -> return [v]
  Nothing -> case rawValue hntt of
   HNApp (Const c) args -> do
    cd <- readIORef c
    case cdcont cd of
     Datatype{} -> g [] args
     _ -> return []
   _ -> return []
 where
  f blks = case blks of
             (_:_) -> case rawValue (last blks) of
              HNApp (Var v) _ -> Just v
              _ -> Nothing
             _ -> Nothing
  g vs args = do
   NotB hnargs <- hnarglist args
   case hnargs of
    HNALCons _ a as -> do
     NotB (_, blks) <- hnn_blks a
     let vs' = case f blks of
                Just v | v `notElem` vs -> v : vs
                _ -> vs
     g vs' as
    _ -> return vs
-- ---------------------------
