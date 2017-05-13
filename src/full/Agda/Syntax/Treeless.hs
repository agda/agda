{-# LANGUAGE DeriveDataTypeable #-}

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

import Data.Map (Map)
import Data.Data (Data)
import Data.Typeable (Typeable)

import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Abstract.Name

data Compiled = Compiled
  { cTreeless :: TTerm
  , cArgUsage :: [Bool] }
  deriving (Typeable, Data, Show, Eq, Ord)

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
           | TCase Int CaseType TTerm [TAlt]
           -- ^ Case scrutinee (always variable), case type, default value, alternatives
           -- First, all TACon alternatives are tried; then all TAGuard alternatives
           -- in top to bottom order.
           -- TACon alternatives must not overlap.
           | TUnit -- used for levels right now
           | TSort
           | TErased
           | TError TError
           -- ^ A runtime error, something bad has happened.
  deriving (Typeable, Data, Show, Eq, Ord)

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
  = PAdd
  | PSub
  | PMul
  | PQuot
  | PRem
  | PGeq
  | PLt
  | PEqI
  | PEqF
  | PEqS
  | PEqC
  | PEqQ
  | PIf
  | PSeq
  deriving (Typeable, Data, Show, Eq, Ord)

isPrimEq :: TPrim -> Bool
isPrimEq p = p `elem` [PEqI, PEqF, PEqS, PEqC, PEqQ]

mkTApp :: TTerm -> Args -> TTerm
mkTApp x           [] = x
mkTApp (TApp x as) bs = TApp x (as ++ bs)
mkTApp x           as = TApp x as

tAppView :: TTerm -> [TTerm]
tAppView = view
  where
    view t = case t of
      TApp a bs -> view a ++ bs
      _         -> [t]

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
tInt = TLit . LitNat noRange

intView :: TTerm -> Maybe Integer
intView (TLit (LitNat _ x)) = Just x
intView _ = Nothing

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
tOp op a b = TApp (TPrim op) [a, b]

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
  deriving (Typeable, Data, Show, Eq, Ord)

data TAlt
  = TACon    { aCon  :: QName, aArity :: Int, aBody :: TTerm }
  -- ^ Matches on the given constructor. If the match succeeds,
  -- the pattern variables are prepended to the current environment
  -- (pushes all existing variables aArity steps further away)
  | TAGuard  { aGuard :: TTerm, aBody :: TTerm }
  -- ^ Binds no variables
  | TALit    { aLit :: Literal,   aBody:: TTerm }
  deriving (Typeable, Data, Show, Eq, Ord)

data TError
  = TUnreachable
  -- ^ Code which is unreachable. E.g. absurd branches or missing case defaults.
  -- Runtime behaviour of unreachable code is undefined, but preferably
  -- the program will exit with an error message. The compiler is free
  -- to assume that this code is unreachable and to remove it.
  deriving (Typeable, Data, Show, Eq, Ord)


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

