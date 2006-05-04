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

-- ! Type of argument lists. Might want to later add hidden info...
--
type Args = [Arg Term]

data Sort = Type Nat
	  | Prop 
	  | MetaS MetaId 
	  | Lub Sort Sort 
  deriving (Typeable, Data)

data Abs a = Abs String a deriving (Typeable, Data)
data Why   = Why	  deriving (Typeable, Data)

--
-- Definitions
--

-- | a clause is a list of patterns and a clause body
--   the number of binding patterns in a clause should
--     match the number of @Bind@s in the body
--
data Clause = Clause [Pattern] ClauseBody deriving (Typeable, Data) 
data ClauseBody = Body Term 
		| Bind (Abs ClauseBody)
  deriving (Typeable, Data)

-- | Patterns are variables, constructors, or wildcards.
--   @QName@ is used in @ConP@ rather than @Name@ since
--     a constructor might come from a particular namespace.
--     This also meshes well with the fact that values (i.e.
--     the arguments we are matching with) use @Name@.
--
data Pattern = VarP Name
	     | ConP QName [Pattern]
             | WildP
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

