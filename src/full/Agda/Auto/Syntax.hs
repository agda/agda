{-# LANGUAGE CPP #-}

module Agda.Auto.Syntax where

import Data.IORef
import qualified Data.Set as Set

import Agda.Syntax.Common (Hiding)
import Agda.Auto.NarrowingSearch

#include "undefined.h"
import Agda.Utils.Impossible

-- | Unique identifiers for variable occurrences in unification.
type UId o = Metavar (Exp o) (RefInfo o)

data HintMode = HMNormal
              | HMRecCall

data EqReasoningConsts o = EqReasoningConsts
  { eqrcId    -- "_≡_"
  , eqrcBegin -- "begin_"
  , eqrcStep  -- "_≡⟨_⟩_"
  , eqrcEnd   -- "_∎"
  , eqrcSym   -- "sym"
  , eqrcCong  -- "cong"
  :: ConstRef o
  }

data EqReasoningState = EqRSNone | EqRSChain | EqRSPrf1 | EqRSPrf2 | EqRSPrf3
 deriving (Eq, Show)

-- | The concrete instance of the 'blk' parameter in 'Metavar'.
--   I.e., the information passed to the search control.

data RefInfo o
  = RIEnv
    { rieHints :: [(ConstRef o, HintMode)]
    , rieDefFreeVars :: Nat
      -- ^ Nat - deffreevars
      --   (to make cost of using module parameters correspond to that of hints).
    , rieEqReasoningConsts :: Maybe (EqReasoningConsts o)
    }
  | RIMainInfo
    { riMainCxtLength :: Nat
      -- ^ Size of typing context in which meta was created.
    , riMainType      :: HNExp o
      -- ^ Head normal form of type of meta.
    , riMainIota      :: Bool
       -- ^ True if iota steps performed when normalising target type
       --   (used to put cost when traversing a definition
       --    by construction instantiation).
    }
  | RIUnifInfo [CAction o] (HNExp o) -- meta environment, opp hne
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

data MId = Id String
         | NoId

-- | Abstraction with maybe a name.
--
--   Different from Agda, where there is also info
--   whether function is constant.
data Abs a = Abs MId a

-- | Constant signatures.

data ConstDef o = ConstDef
  { cdname        :: String
    -- ^ For debug printing.
  , cdorigin      :: o
    -- ^ Reference to the Agda constant.
  , cdtype        :: MExp o
    -- ^ Type of constant.
  , cdcont        :: DeclCont o
    -- ^ Constant definition.
  , cddeffreevars :: Nat
    -- ^ Free vars of the module where the constant is defined..
  } -- contains no metas

-- | Constant definitions.

data DeclCont o
  = Def Nat [Clause o] (Maybe Nat) (Maybe Nat) -- maybe an index to elimand argument, maybe index to elim arg if semiflex
  | Datatype [ConstRef o] -- constructors
             [ConstRef o] -- projection functions (in case it is a record)

  | Constructor Nat -- number of omitted args
  | Postulate

type Clause o = ([Pat o], MExp o)

data Pat o
  = PatConApp (ConstRef o) [Pat o]
  | PatVar String
  | PatExp
    -- ^ Dot pattern.
{- TODO: projection patterns.
  | PatProj (ConstRef o)
    -- ^ Projection pattern.
-}

type ConstRef o = IORef (ConstDef o)

-- | Head of application (elimination).
data Elr o
  = Var Nat
  | Const (ConstRef o)
  deriving (Eq)

data Sort
  = Set Nat
  | UnknownSort
  | Type

-- | Agsy's internal syntax.
data Exp o
  = App
    { appUId   :: Maybe (UId o)
      -- ^ Unique identifier of the head.
    , appOK    :: OKHandle (RefInfo o)
      -- ^ This application has been type-checked.
    , appHead  :: Elr o
      -- ^ Head.
    , appElims :: MArgList o
      -- ^ Arguments.
    }
  | Lam Hiding (Abs (MExp o))
    -- ^ Lambda with hiding information.
  | Pi (Maybe (UId o)) Hiding Bool (MExp o) (Abs (MExp o))
    -- ^ @True@ if possibly dependent (var not known to not occur).
    --   @False@ if non-dependent.
  | Sort Sort
  | AbsurdLambda Hiding
    -- ^ Absurd lambda with hiding information.

dontCare :: Exp o
dontCare = Sort UnknownSort

-- | "Maybe expression":  Expression or reference to meta variable.
type MExp o = MM (Exp o) (RefInfo o)

data ArgList o
  = ALNil
    -- ^ No more eliminations.
  | ALCons Hiding (MExp o) (MArgList o)
    -- ^ Application and tail.

  | ALProj (MArgList o) (MM (ConstRef o) (RefInfo o)) Hiding (MArgList o)
    -- ^ proj pre args, projfcn idx, tail

  | ALConPar (MArgList o)
    -- ^ Constructor parameter (missing in Agda).
    --   Agsy has monomorphic constructors.
    --   Inserted to cover glitch of polymorphic constructor
    --   applications coming from Agda


type MArgList o = MM (ArgList o) (RefInfo o)

data HNExp o = HNApp [Maybe (UId o)] (Elr o) (ICArgList o)
             | HNLam [Maybe (UId o)] Hiding (Abs (ICExp o))
             | HNPi [Maybe (UId o)] Hiding Bool (ICExp o) (Abs (ICExp o))
             | HNSort Sort

-- | Head-normal form of 'ICArgList'.  First entry is exposed.
--
--   Q: Why are there no projection eliminations?
data HNArgList o = HNALNil
                 | HNALCons Hiding (ICExp o) (ICArgList o)
                 | HNALConPar (ICArgList o)

-- | Lazy concatenation of argument lists under explicit substitutions.
data ICArgList o = CALNil
                 | CALConcat (Clos (MArgList o) o) (ICArgList o)

-- | An expression @a@ in an explicit substitution @[CAction a]@.
type ICExp o  = Clos (MExp o) o
data Clos a o = Clos [CAction o] a

type CExp o   = TrBr (ICExp o) o
data TrBr a o = TrBr [MExp o] a

-- | Entry of an explicit substitution.
--
--   An explicit substitution is a list of @CAction@s.
--   This is isomorphic to the usual presentation where
--   @Skip@ and @Weak@ would be constructors of exp. substs.

data CAction o
  = Sub (ICExp o)
    -- ^ Instantation of variable.
  | Skip
    -- ^ For going under a binder, often called "Lift".
  | Weak Nat
    -- ^ Shifting substitution (going to a larger context).

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
weakelr n = rename (n+)

-- | Substituting for a variable.
doclos :: [CAction o] -> Nat -> Either Nat (ICExp o)
doclos = f 0
 where
  -- ns is the number of weakenings
  f ns []            i = Left (ns + i)
  f ns (Weak n : xs) i = f (ns + n) xs i
  f ns (Sub s  : _ ) 0 = Right (weaki ns s)
  f ns (Skip   : _ ) 0 = Left ns
  f ns (Skip   : xs) i = f (ns + 1) xs (i - 1)
  f ns (Sub _  : xs) i = f ns xs (i - 1)


-- | FreeVars class and instances

class FreeVars t where
  freeVars :: t -> Set.Set Nat
  freeVars = freeVarsOffset 0

  freeVarsOffset :: Nat -> t -> Set.Set Nat

instance FreeVars t => FreeVars (MM t a) where
  freeVarsOffset n e = freeVarsOffset n (rm e)

instance FreeVars (Exp o) where
  freeVarsOffset n e = case e of
   App _ _ (Var v) args   -> Set.insert (v - n) (freeVarsOffset n args)
   App _ _ (Const _) args -> freeVarsOffset n args
   Lam _ (Abs _ b)        -> freeVarsOffset (n + 1) b
   Pi _ _ _ it (Abs _ ot) -> Set.union (freeVarsOffset n it)
                                       (freeVarsOffset (n + 1) ot)
   Sort{}                 -> Set.empty
   AbsurdLambda{}         -> Set.empty

instance FreeVars (ArgList o) where
  freeVarsOffset n es = case es of
    ALNil         -> Set.empty
    ALCons _ e es -> Set.union (freeVarsOffset n e) (freeVarsOffset n es)
    ALConPar es   -> freeVarsOffset n es
    ALProj{}      -> __IMPOSSIBLE__


-- | Renaming Typeclass and instances
class Renaming t where
  rename :: (Nat -> Nat) -> t -> t
  rename = renameOffset 0

  renameOffset :: Nat -> (Nat -> Nat) -> t -> t

instance Renaming t => Renaming (MM t a) where
  renameOffset j ren e = NotM $ renameOffset j ren (rm e)

instance Renaming (Elr o) where
  renameOffset j ren e = case e of
    Var v | v >= j -> Var (ren (v - j) + j)
    _              -> e

instance Renaming (Exp o) where
  renameOffset j ren e = case e of
    App uid ok elr args -> App uid ok (renameOffset j ren elr)
                                      (renameOffset j ren args)
    Lam hid (Abs mid e) -> Lam hid (Abs mid (renameOffset (j + 1) ren e))
    Pi uid hid possdep it (Abs mid ot) ->
      Pi uid hid possdep (renameOffset j ren it)
         (Abs mid (renameOffset (j + 1) ren ot))
    Sort{}         -> e
    AbsurdLambda{} -> e

instance Renaming (ArgList o) where
  renameOffset j ren e = case e of
    ALNil           -> ALNil
    ALCons hid a as -> ALCons hid (renameOffset j ren a) (renameOffset j ren as)
    ALConPar as     -> ALConPar (renameOffset j ren as)
    ALProj{}        -> __IMPOSSIBLE__
