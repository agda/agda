{-# OPTIONS -fglasgow-exts #-}

module Syntax.Internal
    ( module Syntax.Internal
    , module Syntax.Abstract.Name
    ) where

import Data.Generics

import Syntax.Common
import Syntax.Literal
import Syntax.Abstract.Name

-- | Raw values.
--
--   @Def@ is used for both defined and undefined constants.
--   Assume there is a type declaration and a definition for
--     every constant, even if the definition is an empty
--     list of clauses.
--
data Term = Var Nat Args
	  | Lam (Abs Term) Args -- ^ allow for redexes
	  | Lit Literal
	  | Def QName Args
	  | Con QName Args
	  | MetaV MetaId Args
  deriving (Typeable, Data)

data Type = El Term Sort
	  | Pi Hiding Type (Abs Type)
	  | Sort Sort
	  | MetaT MetaId Args  -- ^ list of dependencies for metavars
          | LamT (Abs Type) -- ^ abstraction needed for metavar dependency management, !!! is a type necessary?
  deriving (Typeable, Data) 
                            
-- | Type of argument lists.
--                          
type Args = [Arg Term]      
                            
-- | Sequence of types. An argument of the first type is bound in later types
--   and so on.
type Telescope = [Arg Type]

data Sort = Type Nat
	  | Prop 
	  | MetaS MetaId 
	  | Lub Sort Sort
	  | Suc Sort
  deriving (Typeable, Data, Eq)

data Abs a = Abs { absName :: String
		 , absBody :: a
		 }
    deriving (Typeable, Data)

data Why   = Why	  deriving (Typeable, Data)

--
-- Definitions
--

-- | a clause is a list of patterns and a clause body
--   the number of binding patterns in a clause should
--     match the number of @Bind@s in the body
--
data Clause = Clause [Arg Pattern] ClauseBody deriving (Typeable, Data) 
data ClauseBody = Body Term 
		| Bind (Abs ClauseBody)
  deriving (Typeable, Data)

-- | Patterns are variables, constructors, or wildcards.
--   @QName@ is used in @ConP@ rather than @Name@ since
--     a constructor might come from a particular namespace.
--     This also meshes well with the fact that values (i.e.
--     the arguments we are matching with) use @Name@.
--
data Pattern = VarP String  -- name suggestion
	     | ConP QName [Arg Pattern]
  deriving (Typeable, Data)

newtype MetaId = MetaId Nat
    deriving (Eq, Ord, Num, Typeable, Data)

instance Show MetaId where
    show (MetaId n) = show n

---------------------------------------------------------------------------
-- * Smart constructors
---------------------------------------------------------------------------

set0   = Sort (Type 0)
set n  = Sort (Type n)
sort s = Sort s       
prop   = Sort Prop

-- | TODO: name suggestion
telePi :: Telescope -> Type -> Type
telePi [] t = t
telePi (Arg h a : tel) t = Pi h a $ Abs "x" $ telePi tel t

-- | Get the next higher sort.
sSuc :: Sort -> Sort
sSuc Prop	 = Type 1
sSuc (Type n)	 = Type (n + 1)
sSuc (Lub s1 s2) = sSuc s1 `sLub` sSuc s2
sSuc s		 = Suc s

sLub :: Sort -> Sort -> Sort
sLub Prop (Type 0)     = Type 1
sLub (Type 0) Prop     = Prop   -- (x:A) -> B prop if A type0, B prop [x:A]
sLub (Type n) (Type m) = Type $ max n m
sLub s1 s2
    | s1 == s2	= s1
    | otherwise	= Lub s1 s2

