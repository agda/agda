{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE PatternGuards      #-}

{-| Definitions for fixity, precedence levels, and declared syntax.
-}
module Agda.Syntax.Fixity where

import Data.Foldable
import Data.Function
import Data.Hashable
import Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import Data.Typeable (Typeable)

import Agda.Syntax.Position
import Agda.Syntax.Common
import {-# SOURCE #-} qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Notation

import Agda.Utils.List

#include "undefined.h"
import Agda.Utils.Impossible

-- * Notation coupled with 'Fixity'

-- | The notation is handled as the fixity in the renamer.
--   Hence, they are grouped together in this type.
data Fixity' = Fixity'
    { theFixity   :: Fixity
    , theNotation :: Notation
    }
  deriving (Typeable, Show, Eq)

-- | Decorating something with @Fixity'@.
data ThingWithFixity x = ThingWithFixity x Fixity'
  deriving (Functor, Foldable, Traversable, Typeable, Show)

-- | All the notation information related to a name.
data NewNotation = NewNotation
  { notaName   :: QName
  , notaNames  :: Set A.Name
    -- ^ The names the syntax and/or fixity belong to.
    --
    -- Invariant: The set is non-empty. Every name in the list matches
    -- 'notaName'.
  , notaFixity :: Fixity
    -- ^ Associativity and precedence (fixity) of the names.
  , notation   :: Notation
    -- ^ Syntax associated with the names.
  } deriving (Typeable, Show)

-- | If an operator has no specific notation, then it is computed from
-- its name.
namesToNotation :: QName -> A.Name -> NewNotation
namesToNotation q n = NewNotation
  { notaName   = q
  , notaNames  = Set.singleton n
  , notaFixity = f
  , notation   = if null syn then syntaxOf $ unqualify q else syn
  }
  where Fixity' f syn = A.nameFixity n

-- | Return the 'IdPart's of a notation, the first part qualified,
--   the other parts unqualified.
--   This allows for qualified use of operators, e.g.,
--   @M.for x ∈ xs return e@, or @x ℕ.+ y@.
notationNames :: NewNotation -> [QName]
notationNames (NewNotation q _ _ parts) =
  zipWith ($) (reQualify : repeat QName) [Name noRange [Id x] | IdPart x <- parts ]
  where
    -- The qualification of @q@.
    modules     = init (qnameParts q)
    -- Putting the qualification onto @x@.
    reQualify x = List.foldr Qual (QName x) modules

-- | Create a 'Notation' (without binders) from a concrete 'Name'.
--   Does the obvious thing:
--   'Hole's become 'NormalHole's, 'Id's become 'IdParts'.
--   If 'Name' has no 'Hole's, it returns 'noNotation'.
syntaxOf :: Name -> Notation
syntaxOf (NoName _ _) = noNotation
syntaxOf (Name _ [_]) = noNotation
syntaxOf (Name _ xs)  = mkSyn 0 xs
  where
    -- Turn a concrete name into a Notation,
    -- numbering the holes from left to right.
    -- Result will have no 'BindingHole's.
    mkSyn :: Int -> [NamePart] -> Notation
    mkSyn n []          = []
    mkSyn n (Hole : xs) = NormalHole (defaultNamedArg n) : mkSyn (1 + n) xs
    mkSyn n (Id x : xs) = IdPart x : mkSyn n xs

noFixity' :: Fixity'
noFixity' = Fixity' noFixity noNotation

-- | Merges all 'NewNotation's that have the same fixity and notation.
--
-- Precondition: No 'A.Name' may occur in more than one list element.
-- Every 'NewNotation' must have the same 'notaName'.
--
-- Postcondition: No 'A.Name' occurs in more than one list element.
mergeNotations :: [NewNotation] -> [NewNotation]
mergeNotations = map merge . groupOn (\n -> (notation n, notaFixity n))
  where
  merge :: [NewNotation] -> NewNotation
  merge []         = __IMPOSSIBLE__
  merge ns@(n : _) = n { notaNames = Set.unions $ map notaNames ns }

-- * Fixity

-- | Precedence levels for operators.

data PrecedenceLevel = Unrelated | Related Integer
  deriving (Eq, Ord, Show, Typeable)

-- | Associativity.

data Associativity = NonAssoc | LeftAssoc | RightAssoc
   deriving (Eq, Ord, Show, Typeable)

-- | Fixity of operators.

data Fixity =
  Fixity { fixityRange :: Range
         , fixityLevel :: PrecedenceLevel
         , fixityAssoc :: Associativity
         }
  deriving (Typeable, Show)

instance Eq Fixity where
  f1 == f2 = compare f1 f2 == EQ

instance Ord Fixity where
  compare = compare `on` (\f -> (fixityLevel f, fixityAssoc f))

-- For @instance Pretty Fixity@, see Agda.Syntax.Concrete.Pretty

noFixity :: Fixity
noFixity = Fixity noRange Unrelated NonAssoc

-- * Precendence

-- | Precedence is associated with a context.
data Precedence = TopCtx | FunctionSpaceDomainCtx
                | LeftOperandCtx Fixity | RightOperandCtx Fixity
                | FunctionCtx | ArgumentCtx | InsideOperandCtx
                | WithFunCtx | WithArgCtx | DotPatternCtx
    deriving (Show,Typeable, Eq)


-- | The precedence corresponding to a possibly hidden argument.
hiddenArgumentCtx :: Hiding -> Precedence
hiddenArgumentCtx NotHidden = ArgumentCtx
hiddenArgumentCtx Hidden    = TopCtx
hiddenArgumentCtx Instance  = TopCtx

-- | Do we need to bracket an operator application of the given fixity
--   in a context with the given precedence.
opBrackets :: Fixity -> Precedence -> Bool
opBrackets                   (Fixity _ (Related n1) LeftAssoc)
           (LeftOperandCtx   (Fixity _ (Related n2) LeftAssoc))  | n1 >= n2 = False
opBrackets                   (Fixity _ (Related n1) RightAssoc)
           (RightOperandCtx  (Fixity _ (Related n2) RightAssoc)) | n1 >= n2 = False
opBrackets f1
           (LeftOperandCtx  f2) | Related f1 <- fixityLevel f1
                                , Related f2 <- fixityLevel f2
                                , f1 > f2 = False
opBrackets f1
           (RightOperandCtx f2) | Related f1 <- fixityLevel f1
                                , Related f2 <- fixityLevel f2
                                , f1 > f2 = False
opBrackets _ TopCtx = False
opBrackets _ FunctionSpaceDomainCtx = False
opBrackets _ InsideOperandCtx       = False
opBrackets _ WithArgCtx             = False
opBrackets _ WithFunCtx             = False
opBrackets _ _                      = True

-- | Does a lambda-like thing (lambda, let or pi) need brackets in the
-- given context? A peculiar thing with lambdas is that they don't
-- need brackets in certain right operand contexts. However, we insert
-- brackets anyway, for the following reasons:
--
-- * Clarity.
--
-- * Sometimes brackets are needed. Example: @m₁ >>= (λ x → x) >>= m₂@
--   (here @_>>=_@ is left associative).
lamBrackets :: Precedence -> Bool
lamBrackets TopCtx = False
lamBrackets _      = True

-- | Does a function application need brackets?
appBrackets :: Precedence -> Bool
appBrackets ArgumentCtx   = True
appBrackets DotPatternCtx = True
appBrackets _             = False

-- | Does a with application need brackets?
withAppBrackets :: Precedence -> Bool
withAppBrackets TopCtx                 = False
withAppBrackets FunctionSpaceDomainCtx = False
withAppBrackets WithFunCtx             = False
withAppBrackets _                      = True

-- | Does a function space need brackets?
piBrackets :: Precedence -> Bool
piBrackets TopCtx   = False
piBrackets _        = True

roundFixBrackets :: Precedence -> Bool
roundFixBrackets DotPatternCtx = True
roundFixBrackets _ = False

instance HasRange Fixity where
  getRange = fixityRange

instance KillRange Fixity where
  killRange f = f { fixityRange = noRange }

instance KillRange Fixity' where
  killRange (Fixity' f n) = killRange2 Fixity' f n
