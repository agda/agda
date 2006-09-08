{-# OPTIONS -fglasgow-exts #-}

module Syntax.Internal
    ( module Syntax.Internal
    , module Syntax.Abstract.Name
    ) where

import Data.Generics
import Data.FunctorM

import Syntax.Common
import Syntax.Literal
import Syntax.Abstract.Name

import Utils.Monad

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
	  | MetaV MetaId Args
	  | BlockedV (Blocked Term) -- ^ returned by 'TypeChecking.Reduce.reduce'
  deriving (Typeable, Data)

data Type = El Term Sort
	  | Pi (Arg Type) (Abs Type)
	  | Fun (Arg Type) Type
	  | Sort Sort
	  | MetaT MetaId Args	    -- ^ list of dependencies for metavars
          | LamT (Abs Type)	    -- ^ abstraction needed for metavar dependency management
  deriving (Typeable, Data) 

data Sort = Type Nat
	  | Prop 
	  | Lub Sort Sort
	  | Suc Sort
	  | MetaS MetaId 
  deriving (Typeable, Data, Eq)

-- | Something where a particular meta variable blocks reduction.
data Blocked t = Blocked { blockingMeta :: MetaId
			 , blockee	:: t
			 }
    deriving (Typeable, Data, Eq)

instance Functor Blocked where
    fmap f (Blocked m t) = Blocked m $ f t

instance FunctorM Blocked where
    fmapM f (Blocked m t) = Blocked m <$> f t

-- | Type of argument lists.
--                          
type Args = [Arg Term]      
                            
-- | Sequence of types. An argument of the first type is bound in later types
--   and so on.
type Telescope = [Arg (String,Type)]

-- | The body has (at least) one free variable.
data Abs a = Abs { absName :: String
		 , absBody :: a
		 }
    deriving (Typeable, Data)

instance Functor Abs where
    fmap f (Abs x t) = Abs x $ f t

instance FunctorM Abs where 
    fmapM f (Abs x t) = Abs x <$> f t

data Why   = Why	  deriving (Typeable, Data)

--
-- Definitions
--

-- | A clause is a list of patterns and a clause body
--   the number of binding patterns in a clause should
--   match the number of @Bind@s and @NoBind@s in the body
--   The @NoBind@ constructor is an optimisation to avoid
--   substituting for variables that aren't used.
--
data Clause = Clause [Arg Pattern] ClauseBody deriving (Typeable, Data) 
data ClauseBody = Body Term 
		| Bind (Abs ClauseBody)
		| NoBind ClauseBody
  deriving (Typeable, Data)

-- | Patterns are variables, constructors, or wildcards.
--   @QName@ is used in @ConP@ rather than @Name@ since
--     a constructor might come from a particular namespace.
--     This also meshes well with the fact that values (i.e.
--     the arguments we are matching with) use @QName@.
--
data Pattern = VarP String  -- name suggestion
	     | ConP QName [Arg Pattern]
  deriving (Typeable, Data)

newtype MetaId = MetaId Nat
    deriving (Eq, Ord, Num, Typeable, Data)

instance Show MetaId where
    show (MetaId n) = "_" ++ show n


arity :: Type -> Int
arity t =
    case t of
	Pi  (Arg h _) (Abs _ b) -> count h + arity b
	Fun (Arg h _)	     b	-> count h + arity b
	_			-> 0
    where
	count Hidden	= 0
	count NotHidden = 1
   

---------------------------------------------------------------------------
-- * Views
---------------------------------------------------------------------------

data FunView
	= FunV (Arg Type) Type	-- ^ second arg is the entire function ('Pi' or 'Fun').
	| NoFunV Type

funView :: Type -> FunView
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

set0   = Sort (Type 0)
set n  = Sort (Type n)
sort s = Sort s       
prop   = Sort Prop

telePi :: Telescope -> Type -> Type
telePi [] t = t
telePi (Arg h (x,s) : tel) t = Pi (Arg h s) $ Abs x $ telePi tel t

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

