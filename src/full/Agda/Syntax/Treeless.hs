{-# LANGUAGE PatternSynonyms #-}

-- | The treeless syntax is intended to be used as input for the compiler backends.
-- It is more low-level than Internal syntax and is not used for type checking.
--
-- Some of the features of treeless syntax are:
-- - case expressions instead of case trees
-- - no instantiated datatypes / constructors
module Agda.Syntax.Treeless
    ( module Agda.Syntax.Abstract.Name
    , module Agda.Syntax.Treeless
    ) where

import Control.Arrow (first, second)

import Data.Data (Data)
import Data.Word

import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Abstract.Name

data Compiled = Compiled
  { cTreeless :: TTerm
  , cArgUsage :: Maybe [ArgUsage]
      -- ^ 'Nothing' if treeless usage analysis has not run yet.
  }
  deriving (Data, Show, Eq, Ord)

-- | Usage status of function arguments in treeless code.
data ArgUsage
  = ArgUsed
  | ArgUnused
  deriving (Data, Show, Eq, Ord)

-- | The treeless compiler can behave differently depending on the target
--   language evaluation strategy. For instance, more aggressive erasure for
--   lazy targets.
data EvaluationStrategy = LazyEvaluation | EagerEvaluation
  deriving (Eq, Show)

type Args = [TTerm]

-- this currently assumes that TApp is translated in a lazy/cbn fashion.
-- The AST should also support strict translation.
--
-- All local variables are using de Bruijn indices.
data TTerm = TVar Int
           | TPrim TPrim
           | TDef QName
           | TApp TTerm Args
           | TLam TTerm
           | TLit Literal
           | TCon QName
           | TLet TTerm TTerm
           -- ^ introduces a new local binding. The bound term
           -- MUST only be evaluated if it is used inside the body.
           -- Sharing may happen, but is optional.
           -- It is also perfectly valid to just inline the bound term in the body.
           | TCase Int CaseInfo TTerm [TAlt]
           -- ^ Case scrutinee (always variable), case type, default value, alternatives
           -- First, all TACon alternatives are tried; then all TAGuard alternatives
           -- in top to bottom order.
           -- TACon alternatives must not overlap.
           | TUnit -- used for levels right now
           | TSort
           | TErased
           | TCoerce TTerm  -- ^ Used by the GHC backend
           | TError TError
           -- ^ A runtime error, something bad has happened.
  deriving (Data, Show, Eq, Ord)

-- | Compiler-related primitives. This are NOT the same thing as primitives
-- in Agda's surface or internal syntax!
-- Some of the primitives have a suffix indicating which type of arguments they take,
-- using the following naming convention:
-- Char | Type
-- C    | Character
-- F    | Float
-- I    | Integer
-- Q    | QName
-- S    | String
data TPrim
  = PAdd | PAdd64
  | PSub | PSub64
  | PMul | PMul64
  | PQuot | PQuot64
  | PRem  | PRem64
  | PGeq
  | PLt   | PLt64
  | PEqI  | PEq64
  | PEqF
  | PEqS
  | PEqC
  | PEqQ
  | PIf
  | PSeq
  | PITo64 | P64ToI
  deriving (Data, Show, Eq, Ord)

isPrimEq :: TPrim -> Bool
isPrimEq p = p `elem` [PEqI, PEqF, PEqS, PEqC, PEqQ, PEq64]

-- | Strip leading coercions and indicate whether there were some.
coerceView :: TTerm -> (Bool, TTerm)
coerceView = \case
  TCoerce t -> (True,) $ snd $ coerceView t
  t         -> (False, t)

mkTApp :: TTerm -> Args -> TTerm
mkTApp x           [] = x
mkTApp (TApp x as) bs = TApp x (as ++ bs)
mkTApp x           as = TApp x as

tAppView :: TTerm -> (TTerm, [TTerm])
tAppView = \case
  TApp a bs -> second (++ bs) $ tAppView a
  t         -> (t, [])

-- | Expose the format @coerce f args@.
--
--   We fuse coercions, even if interleaving with applications.
--   We assume that coercion is powerful enough to satisfy
--   @
--      coerce (coerce f a) b = coerce f a b
--   @
coerceAppView :: TTerm -> ((Bool, TTerm), [TTerm])
coerceAppView = \case
  TCoerce t -> first ((True,) . snd) $ coerceAppView t
  TApp a bs -> second (++ bs) $ coerceAppView a
  t         -> ((False, t), [])

tLetView :: TTerm -> ([TTerm], TTerm)
tLetView (TLet e b) = first (e :) $ tLetView b
tLetView e          = ([], e)

tLamView :: TTerm -> (Int, TTerm)
tLamView = go 0
  where go n (TLam b) = go (n + 1) b
        go n t        = (n, t)

mkTLam :: Int -> TTerm -> TTerm
mkTLam n b = foldr ($) b $ replicate n TLam

-- | Introduces a new binding
mkLet :: TTerm -> TTerm -> TTerm
mkLet x body = TLet x body

tInt :: Integer -> TTerm
tInt = TLit . LitNat

intView :: TTerm -> Maybe Integer
intView (TLit (LitNat x)) = Just x
intView _ = Nothing

word64View :: TTerm -> Maybe Word64
word64View (TLit (LitWord64 x)) = Just x
word64View _ = Nothing

tPlusK :: Integer -> TTerm -> TTerm
tPlusK 0 n = n
tPlusK k n | k < 0 = tOp PSub n (tInt (-k))
tPlusK k n = tOp PAdd (tInt k) n

-- -(k + n)
tNegPlusK :: Integer -> TTerm -> TTerm
tNegPlusK k n = tOp PSub (tInt (-k)) n

plusKView :: TTerm -> Maybe (Integer, TTerm)
plusKView (TApp (TPrim PAdd) [k, n]) | Just k <- intView k = Just (k, n)
plusKView (TApp (TPrim PSub) [n, k]) | Just k <- intView k = Just (-k, n)
plusKView _ = Nothing

negPlusKView :: TTerm -> Maybe (Integer, TTerm)
negPlusKView (TApp (TPrim PSub) [k, n]) | Just k <- intView k = Just (-k, n)
negPlusKView _ = Nothing

tOp :: TPrim -> TTerm -> TTerm -> TTerm
tOp op a b = TPOp op a b

pattern TPOp :: TPrim -> TTerm -> TTerm -> TTerm
pattern TPOp op a b = TApp (TPrim op) [a, b]

pattern TPFn :: TPrim -> TTerm -> TTerm
pattern TPFn op a = TApp (TPrim op) [a]

tUnreachable :: TTerm
tUnreachable = TError TUnreachable

tIfThenElse :: TTerm -> TTerm -> TTerm -> TTerm
tIfThenElse c i e = TApp (TPrim PIf) [c, i, e]

data CaseType
  = CTData QName -- case on datatype
  | CTNat
  | CTInt
  | CTChar
  | CTString
  | CTFloat
  | CTQName
  deriving (Data, Show, Eq, Ord)

data CaseInfo = CaseInfo
  { caseLazy :: Bool
  , caseType :: CaseType }
  deriving (Data, Show, Eq, Ord)

data TAlt
  = TACon    { aCon  :: QName, aArity :: Int, aBody :: TTerm }
  -- ^ Matches on the given constructor. If the match succeeds,
  -- the pattern variables are prepended to the current environment
  -- (pushes all existing variables aArity steps further away)
  | TAGuard  { aGuard :: TTerm, aBody :: TTerm }
  -- ^ Binds no variables
  | TALit    { aLit :: Literal,   aBody:: TTerm }
  deriving (Data, Show, Eq, Ord)

data TError
  = TUnreachable
  -- ^ Code which is unreachable. E.g. absurd branches or missing case defaults.
  -- Runtime behaviour of unreachable code is undefined, but preferably
  -- the program will exit with an error message. The compiler is free
  -- to assume that this code is unreachable and to remove it.
  | TMeta String
  -- ^ Code which could not be obtained because of a hole in the program.
  -- This should throw a runtime error.
  -- The string gives some information about the meta variable that got compiled.
  deriving (Data, Show, Eq, Ord)


class Unreachable a where
  -- | Checks if the given expression is unreachable or not.
  isUnreachable :: a -> Bool

instance Unreachable TAlt where
  isUnreachable = isUnreachable . aBody

instance Unreachable TTerm where
  isUnreachable (TError TUnreachable{}) = True
  isUnreachable (TLet _ b) = isUnreachable b
  isUnreachable _ = False

instance KillRange Compiled where
  killRange c = c -- bogus, but not used anyway


-- * Utilities for ArgUsage
---------------------------------------------------------------------------

-- | @filterUsed used args@ drops those @args@ which are labelled
-- @ArgUnused@ in list @used@.
--
-- Specification:
--
-- @
--   filterUsed used args = [ a | (a, ArgUsed) <- zip args $ used ++ repeat ArgUsed ]
-- @
--
-- Examples:
--
-- @
--   filterUsed []                 == id
--   filterUsed (repeat ArgUsed)   == id
--   filterUsed (repeat ArgUnused) == const []
-- @
filterUsed :: [ArgUsage] -> [a] -> [a]
filterUsed = curry $ \case
  ([], args) -> args
  (_ , [])   -> []
  (ArgUsed   : used, a : args) -> a : filterUsed used args
  (ArgUnused : used, a : args) ->     filterUsed used args
