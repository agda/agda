{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}

{-| Definitions for fixity, precedence levels, and declared syntax.
-}
module Agda.Syntax.Fixity where

import Data.Foldable
import Data.List as List
import Data.Traversable
import Data.Typeable (Typeable)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Notation

import Agda.Utils.List

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
    -- ^ The concrete name the syntax or fixity belongs to.
  , notaFixity :: Fixity
    -- ^ Associativity and precedence (fixity) of the name.
  , notation   :: Notation
    -- ^ Syntax associated with the name.
  } deriving (Typeable, Show)

-- | If an operator has no specific notation, recover it from its name.
oldToNewNotation :: (QName, Fixity') -> NewNotation
oldToNewNotation (name, Fixity' f syn) = NewNotation
  { notaName   = name
  , notaFixity = f
  , notation   = if null syn then syntaxOf $ unqualify name else syn
  }

-- | Return the 'IdPart's of a notation, the first part qualified,
--   the other parts unqualified.
--   This allows for qualified use of operators, e.g.,
--   @M.for x ∈ xs return e@, or @x ℕ.+ y@.
notationNames :: NewNotation -> [QName]
notationNames (NewNotation q _ parts) =
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

defaultFixity' :: Fixity'
defaultFixity' = Fixity' defaultFixity defaultNotation

-- | Removes copies of @defaultFixity'@ from a list of fixities.
--   Never returns an empty list, though, rather a singleton list
--   consisting of @defaultFixity'@.
interestingFixities :: [Fixity'] -> [Fixity']
interestingFixities fixs = if null fixs' then [defaultFixity'] else fixs'
  where fixs' = filter (not . (== defaultFixity')) fixs

-- | If different interesting fixities are available for the same symbol,
--   we take none of them.
chooseFixity :: [Fixity'] -> Fixity'
chooseFixity fixs = if allEqual fixs' then head fixs' else defaultFixity'
  where fixs' = interestingFixities fixs

-- * Fixity

-- | Fixity of operators.

data Fixity
  = LeftAssoc  { fixityRange :: Range, fixityLevel :: Integer }
  | RightAssoc { fixityRange :: Range, fixityLevel :: Integer }
  | NonAssoc   { fixityRange :: Range, fixityLevel :: Integer }
  deriving (Typeable, Show)

instance Eq Fixity where
    LeftAssoc  _ n == LeftAssoc  _ m = n == m
    RightAssoc _ n == RightAssoc _ m = n == m
    NonAssoc   _ n == NonAssoc   _ m = n == m
    _              == _              = False

-- For @instance Pretty Fixity@, see Agda.Syntax.Concrete.Pretty

-- | The default fixity. Currently defined to be @'NonAssoc' 20@.
defaultFixity :: Fixity
defaultFixity = NonAssoc noRange 20

-- | Hack used for @syntax@ facility.
noFixity :: Fixity
noFixity = NonAssoc noRange (negate 666)
  -- Ts,ts,ts, why the number of the beast?  Revelation 13, 18
  --
  -- It's not the number of the beast, it's the negation of the
  -- number of the beast, which must be a divine number, right?
  --
  -- The divine is not the negation of evil.
  -- Evil is only the absense of the good and divine.


-- * Precendence

-- | Precedence is associated with a context.
data Precedence = TopCtx | FunctionSpaceDomainCtx
                | LeftOperandCtx Fixity | RightOperandCtx Fixity
                | FunctionCtx | ArgumentCtx | InsideOperandCtx
                | WithFunCtx | WithArgCtx | DotPatternCtx
    deriving (Show,Typeable)


-- | The precedence corresponding to a possibly hidden argument.
hiddenArgumentCtx :: Hiding -> Precedence
hiddenArgumentCtx NotHidden = ArgumentCtx
hiddenArgumentCtx Hidden    = TopCtx
hiddenArgumentCtx Instance  = TopCtx

-- | Do we need to bracket an operator application of the given fixity
--   in a context with the given precedence.
opBrackets :: Fixity -> Precedence -> Bool
opBrackets (LeftAssoc _ n1)
           (LeftOperandCtx   (LeftAssoc   _ n2)) | n1 >= n2       = False
opBrackets (RightAssoc _ n1)
           (RightOperandCtx  (RightAssoc  _ n2)) | n1 >= n2       = False
opBrackets f1
           (LeftOperandCtx  f2) | fixityLevel f1 > fixityLevel f2 = False
opBrackets f1
           (RightOperandCtx f2) | fixityLevel f1 > fixityLevel f2 = False
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
  killRange (LeftAssoc  _ n) = LeftAssoc  noRange n
  killRange (RightAssoc _ n) = RightAssoc noRange n
  killRange (NonAssoc   _ n) = NonAssoc   noRange n

instance KillRange Fixity' where
  killRange (Fixity' f n) = killRange1 (flip Fixity' n) f
