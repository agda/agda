{-# LANGUAGE ExistentialQuantification, CPP #-}

module Agda.Auto.Syntax where

import Agda.Utils.Impossible
#include "../undefined.h"

import Data.IORef

import Agda.Auto.NarrowingSearch

type UId o = Metavar (Exp o) (RefInfo o)

data HintMode = HMNormal
              | HMRecCall


data EqReasoningConsts o = EqReasoningConsts {eqrcId, eqrcBegin, eqrcStep, eqrcEnd, eqrcSym, eqrcCong :: ConstRef o} -- "_≡_", "begin_", "_≡⟨_⟩_", "_∎", "sym", "cong"

data EqReasoningState = EqRSNone | EqRSChain | EqRSPrf1 | EqRSPrf2 | EqRSPrf3
 deriving (Eq, Show)


data RefInfo o = RIEnv {rieHints :: [(ConstRef o, HintMode)], rieDefFreeVars :: Nat -- Nat - deffreevars (to make cost of using module parameters correspond to that of hints)

                        , rieEqReasoningConsts :: Maybe (EqReasoningConsts o)

                       }
               | RIMainInfo Nat (HNExp o) Bool -- true if iota steps performed when normalising target type (used to put cost when traversing a definition by construction instantiation)
               | forall a . RIUnifInfo [CAction o] (HNExp o) -- meta environment, opp hne
               | RICopyInfo (ICExp o)
               | RIIotaStep Bool -- True - semiflex
               | RIInferredTypeUnknown
               | RINotConstructor
               | RIUsedVars [UId o] [Elr o]
               | RIPickSubsvar

               | RIEqRState EqReasoningState


               | RICheckElim Bool -- isdep
               | RICheckProjIndex [ConstRef o] -- noof proj functions


type MyPB o = PB (RefInfo o)
type MyMB a o = MB a (RefInfo o)

type Nat = Int


data FMode = Hidden
           | Instance
           | NotHidden
 deriving Eq


data MId = Id String
         | NoId

data Abs a = Abs MId a

data ConstDef o = ConstDef {cdname :: String, cdorigin :: o, cdtype :: MExp o, cdcont :: DeclCont o

                   , cddeffreevars :: Nat

                  } -- contains no metas

data DeclCont o = Def Nat [Clause o] (Maybe Nat) (Maybe Nat) -- maybe an index to elimand argument, maybe index to elim arg if semiflex
                | Datatype [ConstRef o] -- constructors

                           [ConstRef o] -- projection functions

                | Constructor Nat -- number of omitted args
                | Postulate

type Clause o = ([Pat o], MExp o)

data Pat o = PatConApp (ConstRef o) [Pat o]
           | PatVar String
           | PatExp

type ConstRef o = IORef (ConstDef o)

data Elr o = Var Nat
           | Const (ConstRef o)

data Sort = Set Nat

          | UnknownSort

          | Type

data Exp o = App (Maybe (UId o)) (OKHandle (RefInfo o)) (Elr o) (MArgList o)
           | Lam FMode (Abs (MExp o))
           | Pi (Maybe (UId o)) FMode Bool (MExp o) (Abs (MExp o)) -- true if possibly dependent (var not known to not occur)
           | Sort Sort

           | AbsurdLambda FMode


dontCare = Sort UnknownSort


type MExp o = MM (Exp o) (RefInfo o)

data ArgList o = ALNil
               | ALCons FMode (MExp o) (MArgList o)

               | ALProj (MArgList o) (MM (ConstRef o) (RefInfo o)) FMode (MArgList o) -- proj pre args, projfcn idx, tail


               | ALConPar (MArgList o) -- inserted to cover glitch of polymorphic constructor applications coming from Agda


type MArgList o = MM (ArgList o) (RefInfo o)

data HNExp o = HNApp [Maybe (UId o)] (Elr o) (ICArgList o)
             | HNLam [Maybe (UId o)] FMode (Abs (ICExp o))
             | HNPi [Maybe (UId o)] FMode Bool (ICExp o) (Abs (ICExp o))
             | HNSort Sort

data HNArgList o = HNALNil
                 | HNALCons FMode (ICExp o) (ICArgList o)

                 | HNALConPar (ICArgList o)


type ICExp o = Clos (MExp o) o

type CExp o = TrBr (ICExp o) o

data ICArgList o = CALNil
                 | CALConcat (Clos (MArgList o) o) (ICArgList o)

data Clos a o = Clos [CAction o] a
data TrBr a o = TrBr [MExp o] a

data CAction o = Sub (ICExp o)
               | Skip
               | Weak Nat

type Ctx o = [(MId, CExp o)]

type EE = IO

-- -------------------------------------------

detecteliminand :: [Clause o] -> Maybe Nat
detecteliminand cls =
 case map cleli cls of
  [] -> Nothing
  (i:is) -> if all (i ==) is then i else Nothing
 where
  cleli (pats, _) = pateli 0 pats
  pateli i (PatConApp _ args : pats) = if all notcon (args ++ pats) then Just i else Nothing
  pateli i (_ : pats) = pateli (i + 1) pats
  pateli i [] = Nothing
  notcon PatConApp{} = False
  notcon _ = True

detectsemiflex :: ConstRef o -> [Clause o] -> IO Bool
detectsemiflex _ _ = return False -- disabled
categorizedecl :: ConstRef o -> IO ()
categorizedecl c = do
 cd <- readIORef c
 case cdcont cd of
  Def narg cls _ _ -> do
   semif <- detectsemiflex c cls
   let elim = detecteliminand cls
       semifb = case (semif, elim) of
                 (True, Just i) -> Just i -- just copying val of elim arg. this should be changed
                 (_, _) -> Nothing
   writeIORef c (cd {cdcont = Def narg cls elim semifb})
  _ -> return ()

-- -------------------------------------------

metaliseokh :: MExp o -> IO (MExp o)
metaliseokh = fm
 where
  fm (Meta m) = return $ Meta m
  fm (NotM e) = do
   e <- f e
   return $ NotM e
  f (App uid _ elr args) = do
   m <- initMeta
   args <- fms args
   return $ App uid (Meta m) elr args
  f (Lam hid (Abs id b)) = do
   b <- fm b
   return $ Lam hid (Abs id b)
  f (Pi uid hid posdep it (Abs id ot)) = do
   it <- fm it
   ot <- fm ot
   return $ Pi uid hid posdep it (Abs id ot)
  f e@(Sort{}) = return e

  f e@(AbsurdLambda{}) = return e


  fms (Meta m) = return $ Meta m
  fms (NotM es) = do
   es <- fs es
   return $ NotM es
  fs ALNil = return ALNil
  fs (ALCons hid a as) = do
   a <- fm a
   as <- fms as
   return $ ALCons hid a as

  fs (ALProj eas idx hid as) = do
   eas <- fms eas
   as <- fms as
   return $ ALProj eas idx hid as


  fs (ALConPar as) = do
   as <- fms as
   return $ ALConPar as


-- -------------------------------------------

expandExp :: MExp o -> IO (MExp o)
expandExp = fm
 where
  fm (Meta m) = do
   mb <- readIORef $ mbind m
   case mb of
    Nothing -> return $ Meta m
    Just e -> fm (NotM e)
  fm (NotM e) = do
   e <- f e
   return $ NotM e
  f (App uid okh elr args) = do
   args <- fms args
   return $ App uid okh elr args
  f (Lam hid (Abs id b)) = do
   b <- fm b
   return $ Lam hid (Abs id b)
  f (Pi uid hid posdep it (Abs id ot)) = do
   it <- fm it
   ot <- fm ot
   return $ Pi uid hid posdep it (Abs id ot)
  f e@(Sort{}) = return e

  f e@(AbsurdLambda{}) = return e


  fms (Meta m) = do
   mb <- readIORef $ mbind m
   case mb of
    Nothing -> return $ Meta m
    Just es -> fms (NotM es)
  fms (NotM es) = do
   es <- fs es
   return $ NotM es
  fs ALNil = return ALNil
  fs (ALCons hid a as) = do
   a <- fm a
   as <- fms as
   return $ ALCons hid a as

  fs (ALProj eas idx hid as) = do
   idx <- expandbind idx
   eas <- fms eas
   as <- fms as
   return $ ALProj eas idx hid as


  fs (ALConPar as) = do
   as <- fms as
   return $ ALConPar as


-- ---------------------------------

addtrailingargs :: Clos (MArgList o) o -> ICArgList o -> ICArgList o
addtrailingargs newargs CALNil = CALConcat newargs CALNil
addtrailingargs newargs (CALConcat x xs) = CALConcat x (addtrailingargs newargs xs)

-- ---------------------------------

closify :: MExp o -> CExp o
closify e = TrBr [e] (Clos [] e)

sub :: MExp o -> CExp o -> CExp o
-- sub e (Clos [] x) = Clos [Sub e] x
sub e (TrBr trs (Clos (Skip : as) x)) = TrBr (e : trs) (Clos (Sub (Clos [] e) : as) x)
{-sub e (Clos (Weak n : as) x) = if n == 1 then
                                Clos as x
                               else
                                Clos (Weak (n - 1) : as) x-}
sub _ _ = __IMPOSSIBLE__

subi :: MExp o -> ICExp o -> ICExp o
subi e (Clos (Skip : as) x) = Clos (Sub (Clos [] e) : as) x
subi _ _ = __IMPOSSIBLE__

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

doclos :: [CAction o] -> Nat -> Either Nat (ICExp o)
doclos = f 0
 where
  f ns [] i = Left (ns + i)
  f ns (Weak n : xs) i = f (ns + n) xs i
  f ns (Sub s : _) 0 = Right (weaki ns s)
  f ns (Skip : _) 0 = Left ns
  f ns (Skip : xs) i = f (ns + 1) xs (i - 1)
  f ns (Sub _ : xs) i = f ns xs (i - 1)
