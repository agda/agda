{-# LANGUAGE CPP, DeriveDataTypeable, GeneralizedNewtypeDeriving,
             DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Agda.Syntax.Internal
    ( module Agda.Syntax.Internal
    , module Agda.Syntax.Abstract.Name
    ) where

import Prelude hiding (foldr)
import Control.Applicative
import Data.Generics (Typeable, Data)
import Data.Foldable
import Data.Traversable
import Data.Function
import qualified Data.List as List

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Abstract.Name

import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Permutation

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Raw values.
--
--   @Def@ is used for both defined and undefined constants.
--   Assume there is a type declaration and a definition for
--     every constant, even if the definition is an empty
--     list of clauses.
--
data Term = Var Nat Args
	  | Lam Hiding (Abs Term)   -- ^ terms are beta normal
	  | Lit Literal
	  | Def QName Args
	  | Con QName Args
	  | Pi (Arg Type) (Abs Type)
	  | Sort Sort
          | Level Level
	  | MetaV MetaId Args
          | DontCare (Maybe Term)  -- ^ (maybe nuked) irrelevant and other stuff
  deriving (Typeable, Data, Show)
-- Andreas 2010-09-21: @DontCare Nothing@ replaces the hack @Sort Prop@

data Type = El Sort Term
  deriving (Typeable, Data, Show)

data Elim = Apply (Arg Term) | Proj QName -- ^ name of a record projection
  deriving (Show)

-- | Top sort (Set\omega).
topSort :: Type
topSort = El Inf (Sort Inf)

data Sort = Type Level
	  | Prop  -- ignore me
          | Inf
          | DLub Sort (Abs Sort)
            -- ^ if the free variable occurs in the second sort
            --   the whole thing should reduce to Inf, otherwise
            --   it's the normal Lub
  deriving (Typeable, Data, Show)

newtype Level = Max [PlusLevel]
  deriving (Show, Typeable, Data)

data PlusLevel = ClosedLevel Integer
               | Plus Integer LevelAtom
  deriving (Show, Typeable, Data)

data LevelAtom = MetaLevel MetaId Args
               | BlockedLevel MetaId Term
               | NeutralLevel Term
               | UnreducedLevel Term
  deriving (Show, Typeable, Data)

-- | Something where a meta variable may block reduction.
data Blocked t = Blocked MetaId t
               | NotBlocked t
    deriving (Typeable, Data, Eq, Ord, Functor, Foldable, Traversable)

instance Show t => Show (Blocked t) where
  showsPrec p (Blocked m x) = showParen (p > 0) $
    showString "Blocked " . shows m . showString " " . showsPrec 10 x
  showsPrec p (NotBlocked x) = showsPrec p x

instance Applicative Blocked where
  pure = notBlocked
  Blocked x f  <*> e = Blocked x $ f (ignoreBlocking e)
  NotBlocked f <*> e = f <$> e

instance Sized Term where
  size v = case v of
    Var _ vs    -> 1 + Prelude.sum (map size vs)
    Def _ vs    -> 1 + Prelude.sum (map size vs)
    Con _ vs    -> 1 + Prelude.sum (map size vs)
    MetaV _ vs  -> 1 + Prelude.sum (map size vs)
    Level l     -> size l
    Lam _ f     -> 1 + size f
    Lit _       -> 1
    Pi a b      -> 1 + size a + size b
    Sort s      -> 1
    DontCare mv -> size mv

instance Sized Type where
  size = size . unEl

instance Sized Level where
  size (Max as) = 1 + Prelude.sum (map size as)

instance Sized PlusLevel where
  size (ClosedLevel _) = 1
  size (Plus _ a) = size a

instance Sized LevelAtom where
  size (MetaLevel _ vs) = 1 + Prelude.sum (map size vs)
  size (BlockedLevel _ v) = size v
  size (NeutralLevel v) = size v
  size (UnreducedLevel v) = size v

instance KillRange Term where
  killRange v = case v of
    Var i vs    -> killRange1 (Var i) vs
    Def c vs    -> killRange2 Def c vs
    Con c vs    -> killRange2 Con c vs
    MetaV m vs  -> killRange1 (MetaV m) vs
    Lam h f     -> killRange2 Lam h f
    Lit l       -> killRange1 Lit l
    Level l     -> killRange1 Level l
    Pi a b      -> killRange2 Pi a b
    Sort s      -> killRange1 Sort s
    DontCare mv -> killRange1 DontCare mv

instance KillRange Level where
  killRange (Max as) = killRange1 Max as

instance KillRange PlusLevel where
  killRange l@ClosedLevel{} = l
  killRange (Plus n l) = killRange1 (Plus n) l

instance KillRange LevelAtom where
  killRange (MetaLevel n as)   = killRange1 (MetaLevel n) as
  killRange (BlockedLevel m v) = killRange1 (BlockedLevel m) v
  killRange (NeutralLevel v)   = killRange1 NeutralLevel v
  killRange (UnreducedLevel v) = killRange1 UnreducedLevel v

instance KillRange Type where
  killRange (El s v) = killRange2 El s v

instance KillRange Sort where
  killRange s = case s of
    Prop       -> Prop
    Inf        -> Inf
    Type a     -> killRange1 Type a
    DLub s1 s2 -> killRange2 DLub s1 s2

instance KillRange a => KillRange (Tele a) where
  killRange = fmap killRange

{-
-- instance KillRange Telescope where
  killRange EmptyTel = EmptyTel
  killRange (ExtendTel a tel) = ExtendTel (killRange a) (killRange tel) -- killRange2 ExtendTel a tel
-}

instance KillRange a => KillRange (Blocked a) where
  killRange = fmap killRange

instance KillRange a => KillRange (Abs a) where
  killRange = fmap killRange

-- | Type of argument lists.
--
type Args = [Arg Term]

-- | Sequence of types. An argument of the first type is bound in later types
--   and so on.
data Tele a = EmptyTel
	    | ExtendTel a (Abs (Tele a))  -- ^ Abs is never NoAbs.
  deriving (Typeable, Data, Show, Functor, Foldable, Traversable)

type Telescope = Tele (Arg Type)

instance Sized (Tele a) where
  size  EmptyTel	 = 0
  size (ExtendTel _ tel) = 1 + size tel

-- | The body has (at least) one free variable.
data Abs a = Abs String a
           | NoAbs String a
  deriving (Typeable, Data, Functor, Foldable, Traversable)

-- | Danger: doesn't shift variables properly
unAbs :: Abs a -> a
unAbs (Abs   _ v) = v
unAbs (NoAbs _ v) = v

absName :: Abs a -> String
absName (Abs   x _) = x
absName (NoAbs x _) = x

instance Show a => Show (Abs a) where
  showsPrec p (Abs x a) = showParen (p > 0) $
    showString "Abs " . shows x . showString " " . showsPrec 10 a
  showsPrec p (NoAbs x a) = showParen (p > 0) $
    showString "NoAbs " . shows x . showString " " . showsPrec 10 a

instance Sized a => Sized (Abs a) where
  size = size . unAbs

--
-- Definitions
--

-- | A clause is a list of patterns and the clause body should @Bind@.
--
--  The telescope contains the types of the pattern variables and the
--  permutation is how to get from the order the variables occur in
--  the patterns to the order they occur in the telescope. The body
--  binds the variables in the order they appear in the patterns.
--
--  For the purpose of the permutation and the body dot patterns count
--  as variables. TODO: Change this!
data Clause = Clause
    { clauseRange     :: Range
    , clauseTel       :: Telescope
    , clausePerm      :: Permutation
    , clausePats      :: [Arg Pattern]
    , clauseBody      :: ClauseBody
    }
  deriving (Typeable, Data, Show)
data ClauseBody = Body Term
		| Bind (Abs ClauseBody)
		| NoBody    -- ^ for absurd clauses.
  deriving (Typeable, Data, Show)

instance HasRange Clause where
  getRange = clauseRange

-- | Patterns are variables, constructors, or wildcards.
--   @QName@ is used in @ConP@ rather than @Name@ since
--     a constructor might come from a particular namespace.
--     This also meshes well with the fact that values (i.e.
--     the arguments we are matching with) use @QName@.
--
data Pattern = VarP String  -- name suggestion
             | DotP Term
	     | ConP QName (Maybe (Arg Type)) [Arg Pattern]
               -- ^ The type is @'Just' t@' iff the pattern is a
               -- record pattern. The scope used for the type is given
               -- by any outer scope plus the clause's telescope
               -- ('clauseTel').
	     | LitP Literal
  deriving (Typeable, Data, Show)

newtype MetaId = MetaId Nat
    deriving (Eq, Ord, Num, Real, Enum, Integral, Typeable, Data)

instance Show MetaId where
    show (MetaId n) = "_" ++ show n

-- | Doesn't do any reduction.
arity :: Type -> Nat
arity t = case unEl t of
  Pi  _ b -> 1 + arity (unAbs b)
  _       -> 0

-- | Suggest a name for the first argument of a function of the given type.
argName :: Type -> String
argName = argN . unEl
    where
	argN (Pi _ b)  = "." ++ absName b
	argN _	  = __IMPOSSIBLE__


---------------------------------------------------------------------------
-- * Views
---------------------------------------------------------------------------

-- | Viewing an expression as a function type.
data FunView
  = FunV (Arg Type) Term -- ^ First arg is domain, second arg is the entire type ('Pi' or 'Fun').
  | NoFunV Term          -- ^ Expression is not a function type.

{- Andreas, 2011-09-12: DOES NOT WORK, NEED TO MAKE Type a Functor
type FunView = FunV Term
data FunV a
  = FunV (Arg (Type a)) a -- ^ First arg is domain, second arg is the entire type ('Pi' or 'Fun').
  | NoFunV a              -- ^ Expression is not a function type.
-}

-- | Computing the function type view (non-normalizing!),
funView :: Term -> FunView
funView t@(Pi  arg _) = FunV arg t
funView t	      = NoFunV t

---------------------------------------------------------------------------
-- * Smart constructors
---------------------------------------------------------------------------

blockingMeta :: Blocked t -> Maybe MetaId
blockingMeta (Blocked m _) = Just m
blockingMeta (NotBlocked _) = Nothing

blocked :: MetaId -> a -> Blocked a
blocked x = Blocked x

notBlocked :: a -> Blocked a
notBlocked = NotBlocked

ignoreBlocking :: Blocked a -> a
ignoreBlocking (Blocked _ x) = x
ignoreBlocking (NotBlocked x) = x

set0      = set 0
set n     = sort $ mkType n
prop      = sort Prop
sort s    = El (sSuc s) $ Sort s
varSort n = Type $ Max [Plus 0 $ NeutralLevel $ Var n []]

-- | Get the next higher sort.
sSuc :: Sort -> Sort
sSuc Prop            = mkType 1
sSuc Inf             = Inf
sSuc (DLub a b)      = DLub (sSuc a) (fmap sSuc b)
sSuc (Type l)        = Type $ levelSuc l

levelSuc (Max []) = Max [ClosedLevel 1]
levelSuc (Max as) = Max $ map inc as
  where inc (ClosedLevel n) = ClosedLevel (n + 1)
        inc (Plus n l)      = Plus (n + 1) l

mkType n = Type $ Max [ClosedLevel n | n > 0]

teleLam :: Telescope -> Term -> Term
teleLam  EmptyTel	  t = t
teleLam (ExtendTel u tel) t = Lam (argHiding u) $ flip teleLam t <$> tel

getSort :: Type -> Sort
getSort (El s _) = s

unEl :: Type -> Term
unEl (El _ t) = t

impossibleTerm :: String -> Int -> Term
impossibleTerm file line = Lit $ LitString noRange $ unlines
  [ "An internal error has occurred. Please report this as a bug."
  , "Location of the error: " ++ file ++ ":" ++ show line
  ]
