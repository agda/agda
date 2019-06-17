{-# LANGUAGE DeriveDataTypeable #-}

{-| Definitions for fixity, precedence levels, and declared syntax.
-}
module Agda.Syntax.Fixity where

import Prelude hiding (concatMap)

import Control.DeepSeq

import Data.Foldable
import Data.Function
import qualified Data.List as List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable

import Data.Data (Data)

import Agda.Syntax.Position
import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Notation

import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Pretty

import Agda.Utils.Impossible

-- * Notation coupled with 'Fixity'

-- | The notation is handled as the fixity in the renamer.
--   Hence, they are grouped together in this type.
data Fixity' = Fixity'
    { theFixity   :: !Fixity
    , theNotation :: Notation
    , theNameRange :: Range
      -- ^ Range of the name in the fixity declaration
      --   (used for correct highlighting, see issue #2140).
    }
  deriving (Data, Show)

instance Eq Fixity' where
  Fixity' f n _ == Fixity' f' n' _ = f == f' && n == n'

-- | Decorating something with @Fixity'@.
data ThingWithFixity x = ThingWithFixity x Fixity'
  deriving (Functor, Foldable, Traversable, Data, Show)

-- | All the notation information related to a name.
data NewNotation = NewNotation
  { notaName  :: QName
  , notaNames :: Set A.Name
    -- ^ The names the syntax and/or fixity belong to.
    --
    -- Invariant: The set is non-empty. Every name in the list matches
    -- 'notaName'.
  , notaFixity :: Fixity
    -- ^ Associativity and precedence (fixity) of the names.
  , notation :: Notation
    -- ^ Syntax associated with the names.
  , notaIsOperator :: Bool
    -- ^ True if the notation comes from an operator (rather than a
    -- syntax declaration).
  } deriving Show

-- | If an operator has no specific notation, then it is computed from
-- its name.
namesToNotation :: QName -> A.Name -> NewNotation
namesToNotation q n = NewNotation
  { notaName       = q
  , notaNames      = Set.singleton n
  , notaFixity     = f
  , notation       = if null syn then syntaxOf (unqualify q) else syn
  , notaIsOperator = null syn
  }
  where Fixity' f syn _ = A.nameFixity n

-- | Replace 'noFixity' by 'defaultFixity'.
useDefaultFixity :: NewNotation -> NewNotation
useDefaultFixity n
  | notaFixity n == noFixity = n { notaFixity = defaultFixity }
  | otherwise                = n

-- | Return the 'IdPart's of a notation, the first part qualified,
--   the other parts unqualified.
--   This allows for qualified use of operators, e.g.,
--   @M.for x ∈ xs return e@, or @x ℕ.+ y@.
notationNames :: NewNotation -> [QName]
notationNames (NewNotation q _ _ parts _) =
  zipWith ($) (reQualify : repeat QName) [Name noRange InScope [Id $ rangedThing x] | IdPart x <- parts ]
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
syntaxOf (NoName _ _)    = noNotation
syntaxOf (Name _ _ [_])  = noNotation
syntaxOf (Name _ _ xs)   = mkSyn 0 xs
  where
    -- Turn a concrete name into a Notation,
    -- numbering the holes from left to right.
    -- Result will have no 'BindingHole's.
    mkSyn :: Int -> [NamePart] -> Notation
    mkSyn n []          = []
    mkSyn n (Hole : xs) = NormalHole noRange (defaultNamedArg $ unranged n) : mkSyn (1 + n) xs
    mkSyn n (Id x : xs) = IdPart (unranged x) : mkSyn n xs

noFixity' :: Fixity'
noFixity' = Fixity' noFixity noNotation noRange

-- | Merges 'NewNotation's that have the same precedence level and
-- notation, with two exceptions:
--
-- * Operators and notations coming from syntax declarations are kept
--   separate.
--
-- * If /all/ instances of a given 'NewNotation' have the same
--   precedence level or are \"unrelated\", then they are merged. They
--   get the given precedence level, if any, and otherwise they become
--   unrelated (but related to each other).
--
-- If 'NewNotation's that are merged have distinct associativities,
-- then they get 'NonAssoc' as their associativity.
--
-- Precondition: No 'A.Name' may occur in more than one list element.
-- Every 'NewNotation' must have the same 'notaName'.
--
-- Postcondition: No 'A.Name' occurs in more than one list element.
mergeNotations :: [NewNotation] -> [NewNotation]
mergeNotations =
  map merge .
  concatMap groupIfLevelsMatch .
  groupOn (\n -> ( notation n
                 , notaIsOperator n
                 ))
  where
  groupIfLevelsMatch :: [NewNotation] -> [[NewNotation]]
  groupIfLevelsMatch []         = __IMPOSSIBLE__
  groupIfLevelsMatch ns@(n : _) =
    if allEqual (map fixityLevel related)
    then [sameAssoc (sameLevel ns)]
    else map (: []) ns
    where
    -- Fixities of operators whose precedence level is not Unrelated.
    related = mapMaybe (\f -> case fixityLevel f of
                                Unrelated  -> Nothing
                                Related {} -> Just f)
                       (map notaFixity ns)

    -- Precondition: All related operators have the same precedence
    -- level.
    --
    -- Gives all unrelated operators the same level.
    sameLevel = map (set (_notaFixity . _fixityLevel) level)
      where
      level = case related of
        f : _ -> fixityLevel f
        []    -> Unrelated

    -- If all related operators have the same associativity, then the
    -- unrelated operators get the same associativity, and otherwise
    -- all operators get the associativity NonAssoc.
    sameAssoc = map (set (_notaFixity . _fixityAssoc) assoc)
      where
      assoc = case related of
        f : _ | allEqual (map fixityAssoc related) -> fixityAssoc f
        _                                          -> NonAssoc

  merge :: [NewNotation] -> NewNotation
  merge []         = __IMPOSSIBLE__
  merge ns@(n : _) = n { notaNames = Set.unions $ map notaNames ns }

-- * Sections

-- | Sections, as well as non-sectioned operators.

data NotationSection = NotationSection
  { sectNotation  :: NewNotation
  , sectKind      :: NotationKind
    -- ^ For non-sectioned operators this should match the notation's
    -- 'notationKind'.
  , sectLevel     :: Maybe PrecedenceLevel
    -- ^ Effective precedence level. 'Nothing' for closed notations.
  , sectIsSection :: Bool
    -- ^ 'False' for non-sectioned operators.
  }
  deriving Show

-- | Converts a notation to a (non-)section.

noSection :: NewNotation -> NotationSection
noSection n = NotationSection
  { sectNotation  = n
  , sectKind      = notationKind (notation n)
  , sectLevel     = Just (fixityLevel (notaFixity n))
  , sectIsSection = False
  }

-- * Fixity

-- | Precedence levels for operators.

data PrecedenceLevel
  = Unrelated
    -- ^ No fixity declared.
  | Related !Integer
    -- ^ Fixity level declared as the @Integer@.
  deriving (Eq, Ord, Show, Data)

-- | Associativity.

data Associativity = NonAssoc | LeftAssoc | RightAssoc
   deriving (Eq, Ord, Show, Data)

-- | Fixity of operators.

data Fixity = Fixity
  { fixityRange :: Range
    -- ^ Range of the whole fixity declaration.
  , fixityLevel :: !PrecedenceLevel
  , fixityAssoc :: !Associativity
  }
  deriving (Data, Show)

instance Eq Fixity where
  f1 == f2 = compare f1 f2 == EQ

instance Ord Fixity where
  compare = compare `on` (\f -> (fixityLevel f, fixityAssoc f))

-- For @instance Pretty Fixity@, see Agda.Syntax.Concrete.Pretty

noFixity :: Fixity
noFixity = Fixity noRange Unrelated NonAssoc

defaultFixity :: Fixity
defaultFixity = Fixity noRange (Related 20) NonAssoc

-- | Do we prefer parens around arguments like @λ x → x@ or not?
--   See 'lamBrackets'.
data ParenPreference = PreferParen | PreferParenless
  deriving (Eq, Ord, Show, Data)

preferParen :: ParenPreference -> Bool
preferParen p = PreferParen == p

preferParenless :: ParenPreference -> Bool
preferParenless p = PreferParenless == p

-- * Precendence

-- | Precedence is associated with a context.
data Precedence = TopCtx | FunctionSpaceDomainCtx
                | LeftOperandCtx Fixity | RightOperandCtx Fixity ParenPreference
                | FunctionCtx | ArgumentCtx ParenPreference | InsideOperandCtx
                | WithFunCtx | WithArgCtx | DotPatternCtx
    deriving (Show, Data, Eq)

instance Pretty Precedence where
  pretty = text . show

-- | When printing we keep track of a stack of precedences in order to be able
--   to decide whether it's safe to leave out parens around lambdas. An empty
--   stack is equivalent to `TopCtx`. Invariant: `notElem TopCtx`.
type PrecedenceStack = [Precedence]

pushPrecedence :: Precedence -> PrecedenceStack -> PrecedenceStack
pushPrecedence TopCtx _  = []
pushPrecedence p      ps = p : ps

headPrecedence :: PrecedenceStack -> Precedence
headPrecedence []      = TopCtx
headPrecedence (p : _) = p

-- | Argument context preferring parens.
argumentCtx_ :: Precedence
argumentCtx_ = ArgumentCtx PreferParen

-- | Do we need to bracket an operator application of the given fixity
--   in a context with the given precedence.
opBrackets :: Fixity -> PrecedenceStack -> Bool
opBrackets = opBrackets' False

-- | Do we need to bracket an operator application of the given fixity
--   in a context with the given precedence.
opBrackets' :: Bool ->   -- Is the last argument a parenless lambda?
               Fixity -> PrecedenceStack -> Bool
opBrackets' isLam f ps = brack f (headPrecedence ps)
  where
    false = isLam && lamBrackets ps -- require more parens for `e >>= λ x → e₁` than `e >>= e₁`
    brack                        (Fixity _ (Related n1) LeftAssoc)
               (LeftOperandCtx   (Fixity _ (Related n2) LeftAssoc))  | n1 >= n2 = false
    brack                        (Fixity _ (Related n1) RightAssoc)
               (RightOperandCtx  (Fixity _ (Related n2) RightAssoc) _) | n1 >= n2 = false
    brack f1   (LeftOperandCtx  f2) | Related f1 <- fixityLevel f1
                                    , Related f2 <- fixityLevel f2
                                    , f1 > f2 = false
    brack f1   (RightOperandCtx f2 _) | Related f1 <- fixityLevel f1
                                    , Related f2 <- fixityLevel f2
                                    , f1 > f2 = false
    brack _ TopCtx                 = false
    brack _ FunctionSpaceDomainCtx = false
    brack _ InsideOperandCtx       = false
    brack _ WithArgCtx             = false
    brack _ WithFunCtx             = false
    brack _ _                      = True

-- | Does a lambda-like thing (lambda, let or pi) need brackets in the
-- given context? A peculiar thing with lambdas is that they don't
-- need brackets in certain right operand contexts. To decide we need to look
-- at the stack of precedences and not just the current precedence.
-- Example: @m₁ >>= (λ x → x) >>= m₂@ (for @_>>=_@ left associative).
lamBrackets :: PrecedenceStack -> Bool
lamBrackets []       = False
lamBrackets (p : ps) = case p of
  TopCtx                 -> __IMPOSSIBLE__
  ArgumentCtx pref       -> preferParen pref || lamBrackets ps
  RightOperandCtx _ pref -> preferParen pref || lamBrackets ps
  FunctionSpaceDomainCtx -> True
  LeftOperandCtx{}       -> True
  FunctionCtx            -> True
  InsideOperandCtx       -> True
  WithFunCtx             -> True
  WithArgCtx             -> True
  DotPatternCtx          -> True

-- | Does a function application need brackets?
appBrackets :: PrecedenceStack -> Bool
appBrackets = appBrackets' False

-- | Does a function application need brackets?
appBrackets' :: Bool ->   -- Is the argument of the application a parenless lambda?
                PrecedenceStack -> Bool
appBrackets' isLam ps = brack (headPrecedence ps)
  where
    brack ArgumentCtx{} = True
    brack DotPatternCtx = True
    brack _             = isLam && lamBrackets ps -- allow e + e₁ λ x → e₂

-- | Does a with application need brackets?
withAppBrackets :: PrecedenceStack -> Bool
withAppBrackets = brack . headPrecedence
  where
    brack TopCtx                 = False
    brack FunctionSpaceDomainCtx = False
    brack WithFunCtx             = False
    brack _                      = True

-- | Does a function space need brackets?
piBrackets :: PrecedenceStack -> Bool
piBrackets [] = False
piBrackets _  = True

roundFixBrackets :: PrecedenceStack -> Bool
roundFixBrackets ps = DotPatternCtx == headPrecedence ps

instance HasRange Fixity where
  getRange = fixityRange

instance KillRange Fixity where
  killRange f = f { fixityRange = noRange }

instance KillRange Fixity' where
  killRange (Fixity' f n r) = killRange3 Fixity' f n r

instance KillRange x => KillRange (ThingWithFixity x) where
  killRange (ThingWithFixity c f) = ThingWithFixity (killRange c) f

-- * Some lenses

_notaFixity :: Lens' Fixity NewNotation
_notaFixity f r = f (notaFixity r) <&> \x -> r { notaFixity = x }

_fixityAssoc :: Lens' Associativity Fixity
_fixityAssoc f r = f (fixityAssoc r) <&> \x -> r { fixityAssoc = x }

_fixityLevel :: Lens' PrecedenceLevel Fixity
_fixityLevel f r = f (fixityLevel r) <&> \x -> r { fixityLevel = x }

------------------------------------------------------------------------
-- * Printing
------------------------------------------------------------------------

-- deriving instance Show Fixity'

------------------------------------------------------------------------
-- * NFData instances
------------------------------------------------------------------------

instance NFData Fixity' where
  rnf (Fixity' _ a _) = rnf a

-- | Ranges are not forced.

instance NFData Fixity where
  rnf (Fixity _ _ _) = ()
