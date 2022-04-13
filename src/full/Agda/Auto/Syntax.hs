
module Agda.Auto.Syntax where

import Data.IORef
import qualified Data.Set as Set

import Agda.Syntax.Common (Hiding)
import Agda.Auto.NarrowingSearch

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
  | RIUnifInfo [CAction o] (HNExp o)
    -- meta environment, opp hne
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
  = Def Nat [Clause o] (Maybe Nat) -- maybe an index to elimand argument
                       (Maybe Nat) -- maybe index to elim arg if semiflex
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
  | PatProj (ConstRef o)
    -- ^ Projection pattern.

type ConstRef o = IORef (ConstDef o)

-- | Head of application (elimination).
data Elr o
  = Var Nat
  | Const (ConstRef o)
  deriving (Eq)

getVar :: Elr o -> Maybe Nat
getVar (Var n) = Just n
getVar Const{} = Nothing

getConst :: Elr o -> Maybe (ConstRef o)
getConst (Const c) = Just c
getConst Var{}     = Nothing

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

data WithSeenUIds a o = WithSeenUIds
  { seenUIds :: [Maybe (UId o)]
  , rawValue :: a
  }

type HNExp o = WithSeenUIds (HNExp' o) o

data HNExp' o =
    HNApp  (Elr o) (ICArgList o)
  | HNLam  Hiding (Abs (ICExp o))
  | HNPi   Hiding Bool (ICExp o) (Abs (ICExp o))
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

class MetaliseOKH t where
  metaliseOKH :: t -> IO t

instance MetaliseOKH t => MetaliseOKH (MM t a) where
  metaliseOKH = \case
    Meta m -> return $ Meta m
    NotM e -> NotM <$> metaliseOKH e

instance MetaliseOKH t => MetaliseOKH (Abs t) where
  metaliseOKH (Abs id b) = Abs id <$> metaliseOKH b

instance MetaliseOKH (Exp o) where
  metaliseOKH = \case
    App uid okh elr args ->
      (\ m -> App uid m elr) <$> (Meta <$> initMeta) <*> metaliseOKH args
    Lam hid b -> Lam hid <$> metaliseOKH b
    Pi uid hid dep it ot ->
      Pi uid hid dep <$> metaliseOKH it <*> metaliseOKH ot
    e@Sort{} -> return e
    e@AbsurdLambda{} -> return e

instance MetaliseOKH (ArgList o) where
  metaliseOKH = \case
    ALNil -> return ALNil
    ALCons hid a as -> ALCons hid <$> metaliseOKH a <*> metaliseOKH as
    ALProj eas idx hid as ->
      (\ eas -> ALProj eas idx hid) <$> metaliseOKH eas <*> metaliseOKH as
    ALConPar as -> ALConPar <$> metaliseOKH as

metaliseokh :: MExp o -> IO (MExp o)
metaliseokh = metaliseOKH

-- -------------------------------------------

class ExpandMetas t where
  expandMetas :: t -> IO t

instance ExpandMetas t => ExpandMetas (MM t a) where
  expandMetas = \case
    NotM e -> NotM <$> expandMetas e
    Meta m -> do
      mb <- readIORef (mbind m)
      case mb of
        Nothing -> return $ Meta m
        Just e  -> NotM <$> expandMetas e

instance ExpandMetas t => ExpandMetas (Abs t) where
  expandMetas (Abs id b) = Abs id <$> expandMetas b

instance ExpandMetas (Exp o) where
  expandMetas = \case
    App uid okh elr args -> App uid okh elr <$> expandMetas args
    Lam hid b -> Lam hid <$> expandMetas b
    Pi uid hid dep it ot ->
      Pi uid hid dep <$> expandMetas it <*> expandMetas ot
    t@Sort{} -> return t
    t@AbsurdLambda{} -> return t

instance ExpandMetas (ArgList o) where
  expandMetas = \case
    ALNil -> return ALNil
    ALCons hid a as -> ALCons hid <$> expandMetas a <*> expandMetas as
    ALProj eas idx hid as ->
      (\ a b -> ALProj a b hid) <$> expandMetas eas
      <*> expandbind idx <*> expandMetas as
    ALConPar as -> ALConPar <$> expandMetas as

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

weak :: Weakening t => Nat -> t -> t
weak 0 = id
weak n = weak' n

class Weakening t where
  weak' :: Nat -> t -> t

instance Weakening a => Weakening (TrBr a o) where
  weak' n (TrBr trs e) = TrBr trs (weak' n e)

instance Weakening (Clos a o) where
  weak' n (Clos as x) = Clos (Weak n : as) x

instance Weakening (ICArgList o) where
  weak' n = \case
    CALNil         -> CALNil
    CALConcat a as -> CALConcat (weak' n a) (weak' n as)

instance Weakening (Elr o) where
  weak' n = rename (n+)

-- | Substituting for a variable.
doclos :: [CAction o] -> Nat -> Either Nat (ICExp o)
doclos = f 0
 where
  -- ns is the number of weakenings
  f ns []            i = Left (ns + i)
  f ns (Weak n : xs) i = f (ns + n) xs i
  f ns (Sub s  : _ ) 0 = Right (weak ns s)
  f ns (Skip   : _ ) 0 = Left ns
  f ns (Skip   : xs) i = f (ns + 1) xs (i - 1)
  f ns (Sub _  : xs) i = f ns xs (i - 1)


-- | FreeVars class and instances

freeVars :: FreeVars t => t -> Set.Set Nat
freeVars = freeVarsOffset 0

class FreeVars t where
  freeVarsOffset :: Nat -> t -> Set.Set Nat

instance (FreeVars a, FreeVars b) => FreeVars (a, b) where
  freeVarsOffset n (a, b) = Set.union (freeVarsOffset n a) (freeVarsOffset n b)

instance FreeVars t => FreeVars (MM t a) where
  freeVarsOffset n e = freeVarsOffset n (rm __IMPOSSIBLE__ e)

instance FreeVars t => FreeVars (Abs t) where
  freeVarsOffset n (Abs id e) = freeVarsOffset (n + 1) e

instance FreeVars (Elr o) where
  freeVarsOffset n = \case
    Var v   -> Set.singleton (v - n)
    Const{} -> Set.empty

instance FreeVars (Exp o) where
  freeVarsOffset n = \case
   App _ _ elr args -> freeVarsOffset n (elr, args)
   Lam _ b          -> freeVarsOffset n b
   Pi _ _ _ it ot   -> freeVarsOffset n (it, ot)
   Sort{}           -> Set.empty
   AbsurdLambda{}   -> Set.empty

instance FreeVars (ArgList o) where
  freeVarsOffset n es = case es of
    ALNil         -> Set.empty
    ALCons _ e es -> freeVarsOffset n (e, es)
    ALConPar es   -> freeVarsOffset n es
    ALProj{}      -> __IMPOSSIBLE__


-- | Renaming Typeclass and instances
rename :: Renaming t => (Nat -> Nat) -> t -> t
rename = renameOffset 0

class Renaming t where
  renameOffset :: Nat -> (Nat -> Nat) -> t -> t

instance (Renaming a, Renaming b) => Renaming (a, b) where
  renameOffset j ren (a, b) = (renameOffset j ren a, renameOffset j ren b)

instance Renaming t => Renaming (MM t a) where
  renameOffset j ren e = NotM $ renameOffset j ren (rm __IMPOSSIBLE__ e)

instance Renaming t => Renaming (Abs t) where
  renameOffset j ren (Abs id e) = Abs id $ renameOffset (j + 1) ren e

instance Renaming (Elr o) where
  renameOffset j ren = \case
    Var v | v >= j -> Var (ren (v - j) + j)
    e              -> e

instance Renaming (Exp o) where
  renameOffset j ren = \case
    App uid ok elr args -> uncurry (App uid ok) $ renameOffset j ren (elr, args)
    Lam hid e -> Lam hid (renameOffset j ren e)
    Pi a b c it ot -> uncurry (Pi a b c) $ renameOffset j ren (it, ot)
    e@Sort{}         -> e
    e@AbsurdLambda{} -> e

instance Renaming (ArgList o) where
  renameOffset j ren = \case
    ALNil           -> ALNil
    ALCons hid a as -> uncurry (ALCons hid) $ renameOffset j ren (a, as)
    ALConPar as     -> ALConPar (renameOffset j ren as)
    ALProj{}        -> __IMPOSSIBLE__
