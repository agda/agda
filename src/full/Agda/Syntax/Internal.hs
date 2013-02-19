{-# LANGUAGE CPP, DeriveDataTypeable, GeneralizedNewtypeDeriving,
             DeriveFunctor, DeriveFoldable, DeriveTraversable,
             TemplateHaskell,
             MultiParamTypeClasses, FlexibleInstances,
             TypeSynonymInstances #-}

module Agda.Syntax.Internal
    ( module Agda.Syntax.Internal
    , module Agda.Syntax.Abstract.Name
    , module Agda.Utils.Pointer
    ) where

import Prelude hiding (foldr)
import Control.Applicative
import Control.Parallel
import Data.Typeable (Typeable)
import Data.Foldable
import Data.Traversable
import Data.Function
import Data.Maybe
import qualified Data.List as List

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Literal
import Agda.Syntax.Abstract.Name

import Agda.Utils.Geniplate
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Permutation
import Agda.Utils.Pointer

#include "../undefined.h"
import Agda.Utils.Impossible

type Color      = Term
type Arg a      = Common.Arg Color a
type Dom a      = Common.Dom Color a
type NamedArg a = Common.NamedArg Color a
type ArgInfo    = Common.ArgInfo Color

-- | Raw values.
--
--   @Def@ is used for both defined and undefined constants.
--   Assume there is a type declaration and a definition for
--     every constant, even if the definition is an empty
--     list of clauses.
--
data Term = Var {-# UNPACK #-} !Int Args             -- ^ @x vs@ neutral
	  | Lam ArgInfo (Abs Term)   -- ^ Terms are beta normal. Relevance is ignored
	  | Lit Literal
	  | Def QName Args           -- ^ @f vs@, possibly a redex
	  | Con QName Args           -- ^ @c vs@
	  | Pi (Dom Type) (Abs Type) -- ^ dependent or non-dependent function space
	  | Sort Sort
          | Level Level
	  | MetaV {-# UNPACK #-} !MetaId Args
          | DontCare Term
            -- ^ Irrelevant stuff in relevant position, but created
            --   in an irrelevant context.  Basically, an internal
            --   version of the irrelevance axiom @.irrAx : .A -> A@.
          | Shared !(Ptr Term)
            -- ^ Explicit sharing
  deriving (Typeable, Show)

-- | Type of argument lists.
--
type Args = [Arg Term]

-- | Eliminations, subsuming applications and projections.
--   Used for a view which exposes the head of a neutral term.
--
data Elim = Apply (Arg Term) | Proj QName -- ^ name of a record projection
  deriving (Show)

-- | Binder.
--   'Abs': The bound variable might appear in the body.
--   'NoAbs' is pseudo-binder, it does not introduce a fresh variable,
--      similar to the @const@ of Haskell.
data Abs a = Abs   { absName :: String, unAbs :: a }
               -- ^ The body has (at least) one free variable.
               --   Danger: 'unAbs' doesn't shift variables properly
           | NoAbs { absName :: String, unAbs :: a }
  deriving (Typeable, Functor, Foldable, Traversable)

-- | Types are terms with a sort annotation.
--
data Type = El { getSort :: Sort, unEl :: Term }
  deriving (Typeable, Show)

-- | Sequence of types. An argument of the first type is bound in later types
--   and so on.
data Tele a = EmptyTel
	    | ExtendTel a (Abs (Tele a))  -- ^ 'Abs' is never 'NoAbs'.
  deriving (Typeable, Show, Functor, Foldable, Traversable)

type Telescope = Tele (Dom Type)

-- | Sorts.
--
data Sort = Type Level
	  | Prop  -- ignore me
          | Inf
          | DLub Sort (Abs Sort)
            -- ^ if the free variable occurs in the second sort
            --   the whole thing should reduce to Inf, otherwise
            --   it's the normal Lub
  deriving (Typeable, Show)

-- | A level is a maximum expression of 0..n plus expressions
--   each of which is a number or an atom plus a number.
--
newtype Level = Max [PlusLevel]
  deriving (Show, Typeable)

data PlusLevel = ClosedLevel Integer
               | Plus Integer LevelAtom
  deriving (Show, Typeable)

data LevelAtom = MetaLevel MetaId Args
               | BlockedLevel MetaId Term
               | NeutralLevel Term
               | UnreducedLevel Term
  deriving (Show, Typeable)

-- | A meta variable identifier is just a natural number.
--
newtype MetaId = MetaId Nat
    deriving (Eq, Ord, Num, Real, Enum, Integral, Typeable)

-- | Something where a meta variable may block reduction.
data Blocked t = Blocked MetaId t
               | NotBlocked t
    deriving (Typeable, Eq, Ord, Functor, Foldable, Traversable)

instance Applicative Blocked where
  pure = notBlocked
  Blocked x f  <*> e = Blocked x $ f (ignoreBlocking e)
  NotBlocked f <*> e = f <$> e


---------------------------------------------------------------------------
-- * Definitions
---------------------------------------------------------------------------

-- | A clause is a list of patterns and the clause body should @Bind@.
--
--  The telescope contains the types of the pattern variables and the
--  permutation is how to get from the order the variables occur in
--  the patterns to the order they occur in the telescope. The body
--  binds the variables in the order they appear in the patterns.
--
--  @clauseTel ~ permute clausePerm (patternVars clausPats)@
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
  deriving (Typeable, Show)
data ClauseBody = Body Term
		| Bind (Abs ClauseBody)
		| NoBody    -- ^ for absurd clauses.
  deriving (Typeable, Show)

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
  deriving (Typeable, Show)

-- | Extract pattern variables in left-to-right order.
--   A 'DotP' is also treated as variable (see docu for 'Clause').
patternVars :: Arg Pattern -> [Arg (Either String Term)]
patternVars (Common.Arg i (VarP x)     ) = [Common.Arg i $ Left x]
patternVars (Common.Arg i (DotP t)     ) = [Common.Arg i $ Right t]
patternVars (Common.Arg i (ConP _ _ ps)) = List.concat $ map patternVars ps
patternVars (Common.Arg i (LitP l)     ) = []

-- | Does the pattern perform a match that could fail?
properlyMatching :: Pattern -> Bool
properlyMatching VarP{} = False
properlyMatching DotP{} = False
properlyMatching LitP{} = True
properlyMatching (ConP _ mt ps) = List.or $ isNothing mt -- not a record cons
  : map (properlyMatching . unArg) ps  -- or one of subpatterns is a proper m

---------------------------------------------------------------------------
-- * Smart constructors
---------------------------------------------------------------------------

ignoreSharing :: Term -> Term
-- ignoreSharing (Shared p) = ignoreSharing $ derefPtr p
ignoreSharing v          = v

ignoreSharingType :: Type -> Type
-- ignoreSharingType (El s v) = El s (ignoreSharing v)
ignoreSharingType v = v

shared :: Term -> Term
-- shared v@Shared{}   = v
-- shared v@(Var _ []) = v
-- shared v            = Shared (newPtr v)
shared v = v

sharedType :: Type -> Type
-- sharedType (El s v) = El s (shared v)
sharedType v = v

-- | Typically m would be TCM and f would be Blocked.
updateSharedFM :: (Monad m, Applicative m, Traversable f) => (Term -> m (f Term)) -> Term -> m (f Term)
updateSharedFM f v0@(Shared p) = do
  fv <- f (derefPtr p)
  flip traverse fv $ \v ->
    case derefPtr (setPtr v p) of
      Var _ [] -> return v
      _        -> compressPointerChain v0 `pseq` return v0
updateSharedFM f v = f v

updateSharedM :: Monad m => (Term -> m Term) -> Term -> m Term
updateSharedM f v0@(Shared p) = do
  v <- f (derefPtr p)
  case derefPtr (setPtr v p) of
    Var _ [] -> return v
    _        -> compressPointerChain v0 `pseq` return v0
updateSharedM f v = f v

updateShared :: (Term -> Term) -> Term -> Term
updateShared f v0@(Shared p) =
  case derefPtr (setPtr (f $ derefPtr p) p) of
    v@(Var _ []) -> v
    _            -> compressPointerChain v0 `pseq` v0
updateShared f v = f v

pointerChain :: Term -> [Ptr Term]
pointerChain (Shared p) = p : pointerChain (derefPtr p)
pointerChain _          = []

-- Redirect all top-level pointers to point to the last pointer. So, after
-- compression there are at most two top-level indirections.
compressPointerChain :: Term -> Term
compressPointerChain v =
  case reverse $ pointerChain v of
    p:_:ps@(_:_) -> setPointers (Shared p) ps
    _            -> v
  where
    setPointers _ [] = v
    setPointers u (p : ps) =
      setPtr u p `seq` setPointers u ps

-- | An unapplied variable.
var :: Nat -> Term
var i = Var i []

-- | A dummy type.
typeDontCare :: Type
typeDontCare = El Prop (Sort Prop)

-- | Top sort (Set\omega).
topSort :: Type
topSort = El Inf (Sort Inf)

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

impossibleTerm :: String -> Int -> Term
impossibleTerm file line = Lit $ LitString noRange $ unlines
  [ "An internal error has occurred. Please report this as a bug."
  , "Location of the error: " ++ file ++ ":" ++ show line
  ]

---------------------------------------------------------------------------
-- * Handling blocked terms.
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

---------------------------------------------------------------------------
-- * Simple operations on terms and types.
---------------------------------------------------------------------------

-- | Removing a topmost 'DontCare' constructor.
stripDontCare :: Term -> Term
stripDontCare v = case ignoreSharing v of
  DontCare v -> v
  _          -> v

-- | Doesn't do any reduction.
arity :: Type -> Nat
arity t = case ignoreSharing $ unEl t of
  Pi  _ b -> 1 + arity (unAbs b)
  _       -> 0

-- | Suggest a name for the first argument of a function of the given type.
argName :: Type -> String
argName = argN . ignoreSharing . unEl
    where
	argN (Pi _ b)  = "." ++ absName b
	argN _	  = __IMPOSSIBLE__

---------------------------------------------------------------------------
-- * Show instances.
---------------------------------------------------------------------------

instance Show a => Show (Abs a) where
  showsPrec p (Abs x a) = showParen (p > 0) $
    showString "Abs " . shows x . showString " " . showsPrec 10 a
  showsPrec p (NoAbs x a) = showParen (p > 0) $
    showString "NoAbs " . shows x . showString " " . showsPrec 10 a

instance Show MetaId where
    show (MetaId n) = "_" ++ show n

instance Show t => Show (Blocked t) where
  showsPrec p (Blocked m x) = showParen (p > 0) $
    showString "Blocked " . shows m . showString " " . showsPrec 10 x
  showsPrec p (NotBlocked x) = showsPrec p x

---------------------------------------------------------------------------
-- * Sized instances.
---------------------------------------------------------------------------

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
    Shared p    -> size (derefPtr p)

instance Sized Type where
  size = size . unEl

instance Sized Level where
  size (Max as) = 1 + Prelude.sum (map size as)

instance Sized PlusLevel where
  size (ClosedLevel _) = 1
  size (Plus _ a)      = size a

instance Sized LevelAtom where
  size (MetaLevel _   vs) = 1 + Prelude.sum (map size vs)
  size (BlockedLevel _ v) = size v
  size (NeutralLevel   v) = size v
  size (UnreducedLevel v) = size v

instance Sized (Tele a) where
  size  EmptyTel	 = 0
  size (ExtendTel _ tel) = 1 + size tel

instance Sized a => Sized (Abs a) where
  size = size . unAbs

---------------------------------------------------------------------------
-- * KillRange instances.
---------------------------------------------------------------------------

instance KillRange Term where
  killRange v = case v of
    Var i vs    -> killRange1 (Var i) vs
    Def c vs    -> killRange2 Def c vs
    Con c vs    -> killRange2 Con c vs
    MetaV m vs  -> killRange1 (MetaV m) vs
    Lam i f     -> killRange1 Lam i f
    Lit l       -> killRange1 Lit l
    Level l     -> killRange1 Level l
    Pi a b      -> killRange2 Pi a b
    Sort s      -> killRange1 Sort s
    DontCare mv -> killRange1 DontCare mv
    Shared p    -> Shared $ updatePtr killRange p

instance KillRange ArgInfo where
  killRange (Common.ArgInfo h r cs) = killRange2 (flip Common.ArgInfo r) h cs

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

---------------------------------------------------------------------------
-- * UniverseBi instances.
---------------------------------------------------------------------------

instanceUniverseBiT' [] [t| (([Type], [Clause]), Pattern) |]
instanceUniverseBiT' [] [t| (Args, Pattern)               |]
instanceUniverseBiT' [] [t| (([Type], [Clause]), Term)    |]
instanceUniverseBiT' [] [t| (Args, Term)                  |]
instanceUniverseBiT' [] [t| ([Term], Term)                |]
