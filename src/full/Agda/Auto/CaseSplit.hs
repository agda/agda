{-# LANGUAGE CPP                  #-}
{-# LANGUAGE UndecidableInstances #-}

module Agda.Auto.CaseSplit where

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>), (<*>), pure )
#endif

import Data.IORef
import Data.Tuple (swap)
import Data.List (findIndex, union)
import Data.Monoid ((<>), Sum(..))
import Data.Foldable (foldMap)
import qualified Data.Set    as Set
import qualified Data.IntMap as IntMap
import Control.Monad.State as St hiding (lift)
import Control.Monad.Reader as Rd hiding (lift)
import qualified Control.Monad.State as St
import Data.Function

import Agda.Syntax.Common (Hiding(..))
import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax

import Agda.Auto.SearchControl
import Agda.Auto.Typecheck

#include "undefined.h"
import Agda.Utils.Impossible
import Agda.Utils.Monad (or2M)

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
      let r :: [Nat] -> IO [Sol o]
          r [] = return []
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
    case rm __IMPOSSIBLE__ scruttype of
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
          let ff t = case rm __IMPOSSIBLE__ t of
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
                          in hid == NotHidden


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

class Replace o t u | t u -> o where
  replace' :: Nat -> MExp o -> t -> Reader (Nat, Nat) u

replace :: Replace o t u => Nat -> Nat -> MExp o -> t -> u
replace sv nnew e t = replace' 0 e t `runReader` (sv, nnew)

instance Replace o t u => Replace o (Abs t) (Abs u) where
  replace' n re (Abs mid b) = Abs mid <$> replace' (n + 1) re b

instance Replace o (Exp o) (MExp o) where
  replace' n re e = case e of
    App uid ok elr@(Var v) args -> do
      ih         <- NotM <$> replace' n re args
      (sv, nnew) <- ask
      return $
        if v >= n
        then if v - n == sv
             then betareduce (lift n re) ih
             else if v - n > sv
                  then NotM $ App uid ok (Var (v + nnew - 1)) ih
                  else NotM $ App uid ok elr ih
        else NotM $ App uid ok elr ih
    App uid ok elr@Const{} args ->
      NotM . App uid ok elr . NotM <$> replace' n re args
    Lam hid b -> NotM . Lam hid <$> replace' (n + 1) re b
    Pi uid hid possdep it b ->
      fmap NotM $ Pi uid hid possdep <$> replace' n re it <*> replace' n re b
    Sort{} -> return $ NotM e
    AbsurdLambda{} -> return $ NotM e

instance Replace o t u => Replace o (MM t (RefInfo o)) u where
  replace' n re = replace' n re . rm __IMPOSSIBLE__

instance Replace o (ArgList o) (ArgList o) where
  replace' n re args = case args of
    ALNil           -> return ALNil
    ALCons hid a as ->
      ALCons hid <$> replace' n re a <*> (NotM <$> replace' n re as)
    ALProj{}        -> __IMPOSSIBLE__
    ALConPar as     -> ALConPar . NotM <$> replace' n re as


betareduce :: MExp o -> MArgList o -> MExp o
betareduce e args = case rm __IMPOSSIBLE__ args of
 ALNil -> e
 ALCons _ a rargs -> case rm __IMPOSSIBLE__ e of
  App uid ok elr eargs -> NotM $ App uid ok elr (concatargs eargs args)
  Lam _ (Abs _ b) -> betareduce (replace 0 0 a b) rargs
  _ -> __IMPOSSIBLE__ -- not type correct if this happens
 ALProj{} -> __IMPOSSIBLE__
 ALConPar as -> __IMPOSSIBLE__

concatargs :: MArgList o -> MArgList o -> MArgList o
concatargs xs ys = case rm __IMPOSSIBLE__ xs of
  ALNil -> ys

  ALCons hid x xs -> NotM $ ALCons hid x (concatargs xs ys)

  ALProj{} -> __IMPOSSIBLE__

  ALConPar as -> NotM $ ALConPar (concatargs xs ys)

replacep :: forall o. Nat -> Nat -> CSPatI o -> MExp o -> CSPat o -> CSPat o
replacep sv nnew rp re = r
 where
  r :: CSPat o -> CSPat o
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



-- Unification takes two values of the same type and generates a list
-- of assignments making the two terms equal.

type Assignments o = [(Nat, Exp o)]

class Unify o t | t -> o where
  unify'    :: t -> t -> StateT (Assignments o) Maybe ()
  notequal' :: t -> t -> ReaderT (Nat, Nat) (StateT (Assignments o) IO) Bool

unify :: Unify o t => t -> t -> Maybe (Assignments o)
unify t u = unify' t u `execStateT` []

notequal :: Unify o t => Nat -> Nat -> t -> t -> IO Bool
notequal fstnew nbnew t1 t2 = notequal' t1 t2 `runReaderT` (fstnew, nbnew)
                                              `evalStateT` []

instance Unify o t => Unify o (MM t (RefInfo o)) where
  unify' = unify' `on` rm __IMPOSSIBLE__

  notequal' = notequal' `on` rm __IMPOSSIBLE__

unifyVar :: Nat -> Exp o -> StateT (Assignments o) Maybe ()
unifyVar v e = do
  unif <- get
  case lookup v unif of
    Nothing -> modify ((v, e) :)
    Just e' -> unify' e e'

instance Unify o t => Unify o (Abs t) where
  unify' (Abs _ b1) (Abs _ b2) = unify' b1 b2

  notequal' (Abs _ b1) (Abs _ b2) = notequal' b1 b2

instance Unify o (Exp o) where
  unify' e1 e2 = case (e1, e2) of
   (App _ _ elr1 args1, App _ _ elr2 args2) | elr1 == elr2 -> unify' args1 args2
   (Lam hid1 b1, Lam hid2 b2)               | hid1 == hid2 -> unify' b1 b2
   (Pi _ hid1 _ a1 b1, Pi _ hid2 _ a2 b2)   | hid1 == hid2 -> unify' a1 a2
                                                           >> unify' b1 b2
   (Sort _, Sort _) -> return () -- a bit sloppy
   (App _ _ (Var v) (NotM ALNil), _)
     | elem v (freevars e2) -> St.lift Nothing -- Occurs check
   (_, App _ _ (Var v) (NotM ALNil))
     | elem v (freevars e1) -> St.lift Nothing -- Occurs check
   (App _ _ (Var v) (NotM ALNil), _) -> unifyVar v e2
   (_, App _ _ (Var v) (NotM ALNil)) -> unifyVar v e1
   _ -> St.lift Nothing

  notequal' e1 e2 = do
    (fstnew, nbnew) <- ask
    unifier         <- get
    case (e1, e2) of
      (App _ _ elr1 es1, App _ _ elr2 es2) | elr1 == elr2 -> notequal' es1 es2
      (_, App _ _ (Var v2) (NotM ALNil)) -- why is this not symmetric?!
        | fstnew <= v2 && v2 < fstnew + nbnew ->
        case lookup v2 unifier of
          Nothing  -> modify ((v2, e1):) >> return False
          Just e2' -> notequal' e1 e2'
{-
  GA: Skipped these: Not sure why we'd claim they're impossible
      (_, App _ _ (Var v2) (NotM ALProj{})) -> __IMPOSSIBLE__
      (_, App _ _ (Var v2) (NotM ALConPar{})) -> __IMPOSSIBLE__
-}
      (App _ _ (Const c1) es1, App _ _ (Const c2) es2) -> do
        cd1 <- liftIO $ readIORef c1
        cd2 <- liftIO $ readIORef c2
        case (cdcont cd1, cdcont cd2) of
          (Constructor{}, Constructor{}) -> if c1 == c2 then notequal' es1 es2
                                            else return True
          _ -> return False
{- GA: Why don't we have a case for distinct heads after all these
       unification cases for vars with no spines & metas that can
       be looked up?
      (App _ _ elr1 _, App _ _ elr2 _) | elr1 <> elr2 -> return True
-}
      _ -> return False

instance Unify o (ArgList o) where
  unify' args1 args2 = case (args1, args2) of
   (ALNil, ALNil) -> pure ()
   (ALCons hid1 a1 as1, ALCons hid2 a2 as2) | hid1 == hid2 -> unify' a1 a2
                                                           >> unify' as1 as2
   (ALConPar as1, ALCons _ _ as2) -> unify' as1 as2
   (ALCons _ _ as1, ALConPar as2) -> unify' as1 as2
   (ALConPar as1, ALConPar as2)   -> unify' as1 as2
   _ -> St.lift Nothing

  notequal' args1 args2 = case (args1, args2) of
    (ALCons _ e es, ALCons _ f fs) -> notequal' e f `or2M` notequal' es fs
    (ALConPar es1, ALConPar es2)   -> notequal' es1 es2
    _                              -> return False

-- This definition is only here to respect the previous interface.
unifyexp :: MExp o -> MExp o -> Maybe ([(Nat, MExp o)])
unifyexp e1 e2 = fmap (NotM <$>) <$> unify e1 e2

class Lift t where
  lift' :: Nat -> Nat -> t -> t

lift :: Lift t => Nat -> t -> t
lift 0 = id
lift n = lift' n 0

instance Lift t => Lift (Abs t) where
  lift' n j (Abs mid b) = Abs mid (lift' n (j + 1) b)

instance Lift t => Lift (MM t r) where
  lift' n j = NotM . lift' n j . rm __IMPOSSIBLE__

instance Lift (Exp o) where
  lift' n j e = case e of
    App uid ok elr args -> case elr of
      Var v | v >= j -> App uid ok (Var (v + n)) (lift' n j args)
      _ -> App uid ok elr (lift' n j args)
    Lam hid b -> Lam hid (lift' n j b)
    Pi uid hid possdep it b -> Pi uid hid possdep (lift' n j it) (lift' n j b)
    Sort{} -> e
    AbsurdLambda{} -> e

instance Lift (ArgList o) where
  lift' n j args = case args of
    ALNil           -> ALNil
    ALCons hid a as -> ALCons hid (lift' n j a) (lift' n j as)
    ALProj{}        -> __IMPOSSIBLE__
    ALConPar as     -> ALConPar (lift' n j as)


removevar :: CSCtx o -> MExp o -> [CSPat o] -> [(Nat, MExp o)] -> (CSCtx o, MExp o, [CSPat o])
removevar ctx tt pats [] = (ctx, tt, pats)
removevar ctx tt pats ((v, e) : unif) =
 let
  e2 = replace v 0 __IMPOSSIBLE__ {- occurs check failed -} e
  thesub = replace v 0 e2
  ctx1 = map (\(HI hid (id, t)) -> HI hid (id, thesub t)) (take v ctx) ++
         map (\(HI hid (id, t)) -> HI hid (id, thesub t)) (drop (v + 1) ctx)
  tt' = thesub tt
  pats' = map (replacep v 0 (CSPatExp e2) e2) pats
  unif' = map (\(uv, ue) -> (if uv > v then uv - 1 else uv, thesub ue)) unif
 in
  removevar ctx1 tt' pats' unif'

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


freevars :: FreeVars t => t -> [Nat]
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
-- | Speculation: Type class computing the size (?) of a pattern
--   and collecting the vars it introduces
class LocalTerminationEnv a where
  sizeAndBoundVars :: a -> (Sum Nat, [Nat])

instance LocalTerminationEnv a => LocalTerminationEnv (HI a) where
  sizeAndBoundVars (HI _ p) = sizeAndBoundVars p

instance LocalTerminationEnv (CSPatI o) where
  sizeAndBoundVars p = case p of
    CSPatConApp _ ps -> (1, []) <> sizeAndBoundVars ps
    CSPatVar n       -> (0, [n])
    CSPatExp e       -> sizeAndBoundVars e
    _                -> (0, [])

instance LocalTerminationEnv a => LocalTerminationEnv [a] where
  sizeAndBoundVars = foldMap sizeAndBoundVars

instance LocalTerminationEnv (MExp o) where
--  sizeAndBoundVars e = case rm __IMPOSSIBLE__ e of
-- GA: 2017 06 27: Not actually impossible! (cf. #2620)
  sizeAndBoundVars Meta{} = (0, [])
-- Does this default behaviour even make sense? The catchall in the
-- following match seems to suggest it does
  sizeAndBoundVars (NotM e) = case e of
    App _ _ (Var v) _      -> (0, [v])
    App _ _ (Const _) args -> (1, []) <> sizeAndBoundVars args
    _                      -> (0, [])

instance (LocalTerminationEnv a, LocalTerminationEnv b) => LocalTerminationEnv (a, b) where
  sizeAndBoundVars (a, b) = sizeAndBoundVars a <> sizeAndBoundVars b

instance LocalTerminationEnv (MArgList o) where
  sizeAndBoundVars as = case rm __IMPOSSIBLE__ as of
    ALNil         -> (0, [])
    ALCons _ a as -> sizeAndBoundVars (a, as)
    ALProj{}      -> __IMPOSSIBLE__
    ALConPar as   -> sizeAndBoundVars as


-- | Take a list of patterns and returns (is, size, vars) where (speculation):
---  * the is are the pattern indices the vars are contained in
--   * size is total number of constructors removed (?) to access vars
localTerminationEnv :: [CSPat o] -> ([Nat], Nat, [Nat])
localTerminationEnv pats = (is, getSum s, vs) where

  (is , s , vs) = g 0 pats

  g :: Nat -> [CSPat o] -> ([Nat], Sum Nat, [Nat])
  g _ [] = ([], 0, [])
  g i (hp@(HI _ p) : ps) = case p of
    CSPatConApp{} -> let (size, vars) = sizeAndBoundVars hp
                     in ([i], size, vars) <> g (i + 1) ps
    _ -> g (i + 1) ps

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
