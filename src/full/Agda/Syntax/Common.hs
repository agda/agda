{-# LANGUAGE CPP, FlexibleInstances, DeriveDataTypeable,
             DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

{-| Some common syntactic entities are defined in this module.
-}
module Agda.Syntax.Common where

import Data.Typeable (Typeable)
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.Hashable
import Test.QuickCheck

import Agda.Syntax.Position
import Agda.Utils.Monad
import Agda.Utils.Size

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Used to specify whether something should be delayed.
data Delayed = Delayed | NotDelayed
  deriving (Typeable, Show, Eq, Ord)

data Induction = Inductive | CoInductive
  deriving (Typeable, Eq, Ord)

instance Show Induction where
  show Inductive   = "inductive"
  show CoInductive = "coinductive"

instance HasRange Induction where
  getRange _ = noRange

data Hiding  = Hidden | Instance | NotHidden
    deriving (Typeable, Show, Eq, Ord)

instance KillRange Delayed   where killRange = id
instance KillRange Induction where killRange = id
instance KillRange Hiding    where killRange = id

---------------------------------------------------------------------------
-- * Relevance
---------------------------------------------------------------------------

-- | A function argument can be relevant or irrelevant.
--   See 'Agda.TypeChecking.Irrelevance'.
data Relevance
  = Relevant    -- ^ The argument is (possibly) relevant at compile-time.
  | NonStrict   -- ^ The argument may never flow into evaluation position.
                --   Therefore, it is irrelevant at run-time.
                --   It is treated relevantly during equality checking.
  | Irrelevant  -- ^ The argument is irrelevant at compile- and runtime.
  | Forced      -- ^ The argument can be skipped during equality checking
                --   because its value is already determined by the type.
  | UnusedArg   -- ^ The polarity checker has determined that this argument
                --   is unused in the definition.  It can be skipped during
                --   equality checking but should be mined for solutions
                --   of meta-variables with relevance 'UnusedArg'
    deriving (Typeable, Show, Eq, Enum, Bounded)

instance Arbitrary Relevance where
  arbitrary = elements [minBound..maxBound]

instance Ord Relevance where
  (<=) = moreRelevant

-- | Information ordering.
-- @Relevant  \`moreRelevant\`
--  UnusedArg \`moreRelevant\`
--  Forced    \`moreRelevant\`
--  NonStrict \`moreRelevant\`
--  Irrelevant@
moreRelevant :: Relevance -> Relevance -> Bool
moreRelevant r r' =
  case (r, r') of
    -- top
    (_, Irrelevant) -> True
    (Irrelevant, _) -> False
    -- bottom
    (Relevant, _)   -> True
    (_, Relevant)   -> False
    -- second bottom
    (UnusedArg, _)  -> True
    (_, UnusedArg)  -> False
    -- third bottom
    (Forced, _)     -> True
    (_, Forced)     -> False
    -- remaining case
    (NonStrict,NonStrict) -> True

---------------------------------------------------------------------------
-- * Function type domain
---------------------------------------------------------------------------

-- | Similar to 'Arg', but we need to distinguish
--   an irrelevance annotation in a function domain
--   (the domain itself is not irrelevant!)
--   from an irrelevant argument.
--
--   @Dom@ is used in 'Pi' of internal syntax, in 'Context' and 'Telescope'.
--   'Arg' is used for actual arguments ('Var', 'Con', 'Def' etc.)
--   and in 'Abstract' syntax and other situations.
data Dom c e = Dom
  { domInfo   :: ArgInfo c
  , unDom     :: e
  } deriving (Typeable, Eq, Ord, Functor, Foldable, Traversable)

domHiding    = argInfoHiding    . domInfo
domRelevance = argInfoRelevance . domInfo
domColors    = argInfoColors    . domInfo

argFromDom :: Dom c a -> Arg c a
argFromDom (Dom i a) = Arg i a

domFromArg :: Arg c a -> Dom c a
domFromArg (Arg i a) = Dom i a

mapDomHiding :: (Hiding -> Hiding) -> Dom c a -> Dom c a
mapDomHiding f = domFromArg . mapArgHiding f . argFromDom

mapDomRelevance :: (Relevance -> Relevance) -> Dom c a -> Dom c a
mapDomRelevance f = domFromArg . mapArgRelevance f . argFromDom

instance HasRange a => HasRange (Dom c a) where
    getRange = getRange . unDom

instance KillRange a => KillRange (Dom c a) where
  killRange = fmap killRange

instance Sized a => Sized (Dom c a) where
  size = size . unDom

instance (Show a, Show c) => Show (Dom c a) where
    show = show . argFromDom

---------------------------------------------------------------------------
-- * Argument decoration
---------------------------------------------------------------------------

-- | A function argument can be hidden and/or irrelevant.
data Arg c e  = Arg
  { argInfo :: ArgInfo c
  , unArg :: e
  } deriving (Typeable, Ord, Functor, Foldable, Traversable)

data ArgInfo c = ArgInfo
  { argInfoHiding    :: Hiding
  , argInfoRelevance :: Relevance
  , argInfoColors    :: [c]
  } deriving (Typeable, Eq, Ord, Functor, Foldable, Traversable, Show)

argHiding    = argInfoHiding    . argInfo
argRelevance = argInfoRelevance . argInfo
argColors    = argInfoColors    . argInfo

instance (Eq a, Eq c) => Eq (Arg c a) where
  Arg (ArgInfo h1 _ cs1) x1 == Arg (ArgInfo h2 _ cs2) x2 = (h1, cs1, x1) == (h2, cs2, x2)

mapArgInfo :: (ArgInfo c -> ArgInfo c') -> Arg c a -> Arg c' a
mapArgInfo f arg = arg { argInfo = f $ argInfo arg }

mapArgInfoHiding :: (Hiding -> Hiding) -> ArgInfo c -> ArgInfo c
mapArgInfoHiding f info = info { argInfoHiding = f $ argInfoHiding info }

mapArgInfoRelevance :: (Relevance -> Relevance) -> ArgInfo c -> ArgInfo c
mapArgInfoRelevance f info = info { argInfoRelevance = f $ argInfoRelevance info }

mapArgInfoColors :: ([c] -> [c']) -> ArgInfo c -> ArgInfo c'
mapArgInfoColors f info = info { argInfoColors = f $ argInfoColors info }

mapArgHiding :: (Hiding -> Hiding) -> Arg c a -> Arg c a
mapArgHiding = mapArgInfo . mapArgInfoHiding

mapArgRelevance :: (Relevance -> Relevance) -> Arg c a -> Arg c a
mapArgRelevance = mapArgInfo . mapArgInfoRelevance

mapArgColors :: ([c] -> [c']) -> Arg c a -> Arg c' a
mapArgColors = mapArgInfo . mapArgInfoColors

setArgInfoHiding :: Hiding -> ArgInfo c -> ArgInfo c
setArgInfoHiding = mapArgInfoHiding . const

setArgInfoRelevance :: Relevance -> ArgInfo c -> ArgInfo c
setArgInfoRelevance = mapArgInfoRelevance . const

setArgHiding :: Hiding -> Arg c a -> Arg c a
setArgHiding = mapArgHiding . const

setArgRelevance :: Relevance -> Arg c a -> Arg c a
setArgRelevance = mapArgRelevance . const

setArgColors :: [c] -> Arg c' a -> Arg c a
setArgColors = mapArgColors . const

makeInstance :: Arg c a -> Arg c a
makeInstance = setArgHiding Instance

hide :: Arg c a -> Arg c a
hide = setArgHiding Hidden

defaultArgInfo :: ArgInfo c
defaultArgInfo =  ArgInfo { argInfoHiding    = NotHidden
                          , argInfoRelevance = Relevant
                          , argInfoColors    = [] }

defaultArg :: a -> Arg c a
defaultArg = Arg defaultArgInfo

defaultColoredArg :: ([c],a) -> Arg c a
defaultColoredArg (cs,a) = setArgColors cs $ defaultArg a

noColorArg :: Hiding -> Relevance -> a -> Arg c a
noColorArg h r = Arg $ ArgInfo { argInfoHiding    = h
                               , argInfoRelevance = r
                               , argInfoColors    = []
                               }

isHiddenArg :: Arg c a -> Bool
isHiddenArg arg = argHiding arg /= NotHidden

isArgInfoHidden    info = argInfoHiding info == Hidden
isArgInfoNotHidden info = argInfoHiding info == NotHidden

isArgInfoRelevant   info = argInfoRelevance info == Relevant
isArgInfoIrrelevant info = argInfoRelevance info == Irrelevant

-- | @xs \`withArgsFrom\` args@ translates @xs@ into a list of 'Arg's,
-- using the elements in @args@ to fill in the non-'unArg' fields.
--
-- Precondition: The two lists should have equal length.

withArgsFrom :: [a] -> [Arg c b] -> [Arg c a]
xs `withArgsFrom` args =
  zipWith (\x arg -> fmap (const x) arg) xs args

instance HasRange a => HasRange (Arg c a) where
    getRange = getRange . unArg

instance KillRange a => KillRange (Arg c a) where
  killRange = fmap killRange

instance Sized a => Sized (Arg c a) where
  size = size . unArg

instance (Show a, Show c) => Show (Arg c a) where
    show (Arg (ArgInfo h r cs) x) = showC cs $ showR r $ showH h $ show x
      where
        showH Hidden     s = "{" ++ s ++ "}"
        showH NotHidden  s = "(" ++ s ++ ")"
        showH Instance   s = "{{" ++ s ++ "}}"
        showR Irrelevant s = "." ++ s
        showR NonStrict  s = "?" ++ s
        showR Forced     s = "!" ++ s
        showR UnusedArg  s = "k" ++ s -- constant
        showR Relevant   s = "r" ++ s -- Andreas: I want to see it explicitly
        showC cs         s = show cs ++ s

---------------------------------------------------------------------------
-- * Named arguments
---------------------------------------------------------------------------

data Named name a =
    Named { nameOf     :: Maybe name
	  , namedThing :: a
	  }
    deriving (Eq, Ord, Typeable, Functor, Foldable, Traversable)

unnamed :: a -> Named name a
unnamed = Named Nothing

named :: name -> a -> Named name a
named = Named . Just

instance HasRange a => HasRange (Named name a) where
    getRange = getRange . namedThing

instance KillRange a => KillRange (Named name a) where
  killRange = fmap killRange

instance Sized a => Sized (Named name a) where
  size = size . namedThing

instance Show a => Show (Named String a) where
    show (Named Nothing x)  = show x
    show (Named (Just n) x) = n ++ " = " ++ show x

-- | Only 'Hidden' arguments can have names.
type NamedArg c a = Arg c (Named String a)

-- | Get the content of a 'NamedArg'.
namedArg :: NamedArg c a -> a
namedArg = namedThing . unArg

defaultNamedArg :: a -> NamedArg c a
defaultNamedArg = defaultArg . unnamed

-- | The functor instance for 'NamedArg' would be ambiguous,
--   so we give it another name here.
updateNamedArg :: (a -> b) -> NamedArg c a -> NamedArg c b
updateNamedArg = fmap . fmap

---------------------------------------------------------------------------
-- * Infixity, access, abstract, etc.
---------------------------------------------------------------------------

-- | Functions can be defined in both infix and prefix style. See
--   'Agda.Syntax.Concrete.LHS'.
data IsInfix = InfixDef | PrefixDef
    deriving (Typeable, Show, Eq, Ord)

-- | Access modifier.
data Access = PrivateAccess | PublicAccess
            | OnlyQualified  -- ^ Visible from outside, but not exported when opening the module
                             --   Used for qualified constructors.
    deriving (Typeable, Show, Eq, Ord)

-- | Abstract or concrete
data IsAbstract = AbstractDef | ConcreteDef
    deriving (Typeable, Show, Eq, Ord)

type Nat    = Int
type Arity  = Nat

-- | The unique identifier of a name. Second argument is the top-level module
--   identifier.
data NameId = NameId Integer Integer
    deriving (Eq, Ord, Typeable)

instance Enum NameId where
  succ (NameId n m)	= NameId (n + 1) m
  pred (NameId n m)	= NameId (n - 1) m
  toEnum n		= __IMPOSSIBLE__  -- should not be used
  fromEnum (NameId n _) = fromIntegral n

instance Hashable NameId where
  {-# INLINE hashWithSalt #-}
  hashWithSalt salt (NameId n m) = hashWithSalt salt (n, m)

newtype Constr a = Constr a

------------------------------------------------------------------------
-- Arbitrary and CoArbitrary instances

instance Arbitrary Induction where
  arbitrary = elements [Inductive, CoInductive]

instance CoArbitrary Induction where
  coarbitrary Inductive   = variant 0
  coarbitrary CoInductive = variant 1
