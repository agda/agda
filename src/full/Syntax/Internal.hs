{-# OPTIONS -fglasgow-exts -cpp #-}

module Syntax.Internal
    ( module Syntax.Internal
    , module Syntax.Abstract.Name
    ) where

import Prelude hiding (foldr)
import Control.Applicative
import Data.Generics
import Data.Foldable
import Data.Traversable

import Syntax.Common
import Syntax.Literal
import Syntax.Abstract.Name

import Utils.Monad
import Utils.Size

#include "../undefined.h"

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
	  | Fun (Arg Type) Type
	  | Sort Sort
	  | MetaV MetaId Args
	  | BlockedV (Blocked Term) -- ^ returned by 'TypeChecking.Reduce.reduce'
  deriving (Typeable, Data, Eq, Show)

data Type = El Sort Term
  deriving (Typeable, Data, Eq, Show)

data Sort = Type Nat
	  | Prop 
	  | Lub Sort Sort
	  | Suc Sort
	  | MetaS MetaId 
  deriving (Typeable, Data, Eq, Show)

-- | Something where a particular meta variable blocks reduction.
data Blocked t = Blocked { blockingMeta :: MetaId
			 , blockee	:: t
			 }
    deriving (Typeable, Data, Eq)

instance Show t => Show (Blocked t) where
  showsPrec p (Blocked m x) = showParen (p > 0) $
    showString "Blocked " . shows m . showString " " . showsPrec 10 x

instance Functor Blocked where
    fmap f (Blocked m t) = Blocked m $ f t

instance Foldable Blocked where
    foldr f z (Blocked _ x) = f x z

instance Traversable Blocked where
    traverse f (Blocked m t) = Blocked m <$> f t

instance Sized Term where
  size v = case v of
    Var _ vs   -> 1 + Prelude.sum (map size vs)
    Def _ vs   -> 1 + Prelude.sum (map size vs)
    Con _ vs   -> 1 + Prelude.sum (map size vs)
    MetaV _ vs -> 1 + Prelude.sum (map size vs)
    Lam _ f    -> 1 + size f
    Lit _      -> 1
    Pi a b     -> 1 + size a + size b
    Fun a b    -> 1 + size a + size b
    Sort s     -> 1
    BlockedV b -> size (blockee b)

instance Sized Type where
  size = size . unEl

-- | Type of argument lists.
--                          
type Args = [Arg Term]      
                            
-- | Sequence of types. An argument of the first type is bound in later types
--   and so on.
data Telescope = EmptyTel
	       | ExtendTel (Arg Type) (Abs Telescope)
  deriving (Typeable, Data, Show, Eq)

instance Sized Telescope where
  size  EmptyTel	 = 0
  size (ExtendTel _ tel) = 1 + size tel

-- | The body has (at least) one free variable.
data Abs a = Abs { absName :: String
		 , absBody :: a
		 }
  deriving (Typeable, Data, Eq)

instance Show a => Show (Abs a) where
  showsPrec p (Abs x a) = showParen (p > 0) $
    showString "Abs " . shows x . showString " " . showsPrec 10 a

instance Functor Abs where
  fmap f (Abs x t) = Abs x $ f t

instance Foldable Abs where
  foldr f z (Abs _ t) = f t z

instance Traversable Abs where 
  traverse f (Abs x t) = Abs x <$> f t

instance Sized a => Sized (Abs a) where
  size = size . absBody

telFromList :: [Arg (String, Type)] -> Telescope
telFromList = foldr (\(Arg h (x, a)) -> ExtendTel (Arg h a) . Abs x) EmptyTel

telToList :: Telescope -> [Arg (String, Type)]
telToList EmptyTel = []
telToList (ExtendTel arg (Abs x tel)) = fmap ((,) x) arg : telToList tel

--
-- Definitions
--

-- | A clause is a list of patterns and a clause body
--   the number of binding patterns in a clause should
--   match the number of @Bind@s and @NoBind@s in the body
--   The @NoBind@ constructor is an optimisation to avoid
--   substituting for variables that aren't used.
--
data Clause = Clause [Arg Pattern] ClauseBody deriving (Typeable, Data, Show)
data ClauseBody = Body Term 
		| Bind (Abs ClauseBody)
		| NoBind ClauseBody
		| NoBody    -- for absurd clauses
  deriving (Typeable, Data, Show)

-- | Patterns are variables, constructors, or wildcards.
--   @QName@ is used in @ConP@ rather than @Name@ since
--     a constructor might come from a particular namespace.
--     This also meshes well with the fact that values (i.e.
--     the arguments we are matching with) use @QName@.
--
data Pattern = VarP String  -- name suggestion
             | DotP Term
	     | ConP QName [Arg Pattern]
	     | LitP Literal
  deriving (Typeable, Data, Show)

newtype MetaId = MetaId Nat
    deriving (Eq, Ord, Num, Typeable, Data)

instance Show MetaId where
    show (MetaId n) = "_" ++ show n

-- | Doesn't do any reduction.
arity :: Type -> Int
arity t =
    case unEl t of
	Pi  _ (Abs _ b) -> 1 + arity b
	Fun _	     b	-> 1 + arity b
	_		-> 0

-- | Suggest a name for the first argument of a function of the given type.
argName :: Type -> String
argName = argN . unEl
    where
	argN (Pi _ b)  = "." ++ absName b
	argN (Fun _ _) = ".x"
	argN _	  = __IMPOSSIBLE__


---------------------------------------------------------------------------
-- * Views
---------------------------------------------------------------------------

data FunView
	= FunV (Arg Type) Term	-- ^ second arg is the entire type ('Pi' or 'Fun').
	| NoFunV Term

funView :: Term -> FunView
funView t@(Pi  arg _) = FunV arg t
funView t@(Fun arg _) = FunV arg t
funView t	      = NoFunV t

---------------------------------------------------------------------------
-- * Smart constructors
---------------------------------------------------------------------------

blocked :: MetaId -> Term -> Term
blocked x t = BlockedV $ Blocked x t

ignoreBlocking :: Term -> Term
ignoreBlocking (BlockedV b) = blockee b
ignoreBlocking v	    = v

set0   = sort (Type 0)
set n  = sort (Type n)
prop   = sort Prop
sort s = El (sSuc s) $ Sort s

teleLam :: Telescope -> Term -> Term
teleLam  EmptyTel	  t = t
teleLam (ExtendTel u tel) t = Lam (argHiding u) $ flip teleLam t <$> tel

getSort :: Type -> Sort
getSort (El s _) = s

unEl :: Type -> Term
unEl (El _ t) = t

-- | Get the next higher sort.
sSuc :: Sort -> Sort
sSuc Prop	 = Type 1
sSuc (Type n)	 = Type (n + 1)
sSuc (Lub s1 s2) = sSuc s1 `sLub` sSuc s2
sSuc s		 = Suc s

sLub :: Sort -> Sort -> Sort
sLub (Type 0) Prop     = Prop   -- (x:A) -> B prop if A type0, B prop [x:A]
sLub (Type n) Prop     = Type n
sLub Prop (Type n)     = Type n
sLub (Type n) (Type m) = Type $ max n m
sLub s1 s2
    | s1 == s2	= s1
    | otherwise	= Lub s1 s2

