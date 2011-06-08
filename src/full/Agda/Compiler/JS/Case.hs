module Agda.Compiler.JS.Case where

import Prelude hiding ( null )
import Data.Map ( Map, empty, null, mapWithKey, fromListWith, unionWith )
import Data.List ( genericLength, genericTake )

import Agda.Syntax.Common ( Nat )

import Agda.Compiler.JS.LambdaC
  ( Exp(Undefined,Local,Lambda,Object,Apply,Lookup),
    LocalId(LocalId), MemberId, shift )

-- ECMAScript doesn't support pattern-mathching case, so
-- we translate to a visitor pattern.  We use a decision-tree
-- translation, as that seems to fit visitor objects better.

data Case = Case { pats :: [Patt], body :: Exp }
  deriving (Show)

-- Not handling literal patterns yet
-- Note that all patterns introduce binders, in depth-first prefix order,
-- for example Tagged l [ VarPatt , VarPatt ] should be thought
-- of as "x2 @ l (x1, x0)".

data Patt =
  VarPatt |
  Tagged Tag [Patt]
  deriving (Show)

-- With each tag, we record its name, and the names of the
-- other constructors of the datatype (e.g. we'd represent
-- zero as Tag "zero" ["suc","zero"]).  We also record the
-- the function which accepts a visitor (by default Apply,
-- but can be over-ridden by the FFI).

data Tag = Tag MemberId [MemberId] (Exp -> [Exp] ->  Exp)

instance Show Tag where
  show (Tag i is _) = show i

-- Compile a case statement to a function
-- in lambda n cs, n is the number of parameters

lambda :: [Case] -> Exp
lambda []     = Undefined
lambda (c:cs) = lambda' 0 (genericLength (pats c)) (c:cs)

-- In lambda m n cs, m is the number of already read parameters, n is the number of unread parameters

lambda' :: Nat -> Nat -> [Case] -> Exp
lambda' m n []       = Undefined
lambda' 0 0 (c : cs) = body c
lambda' 0 n cs       = Lambda 1 (lambda' 1 (n-1) cs)
lambda' m n cs       =
  case null ts of
    True -> lambda' (m-1) n (map pop cs)
    False -> visit cs (Local (LocalId (m-1))) [Object (mapWithKey (match (m-1) n cs) ts)]
  where
    ts = tags cs

-- Pop cases

pop :: Case -> Case
pop (Case []       e) = (Case [] e)
pop (Case (p : ps) e) = (Case ps e) -- Need to shift?

-- Cases which match a given tag/arity

match :: Nat -> Nat -> [Case] -> MemberId -> Nat -> Exp
match m n cs l x = Lambda x (lambda' (m + x) n (concat (map (refine l x) cs)))

-- Refine a case statement by a given tag/arity

refine :: MemberId -> Nat -> Case -> [Case]
refine l n (Case [] e) =
  [Case (genericTake n (repeat VarPatt)) (shift n e)]
refine l n (Case (VarPatt : qs) e) =
  [Case (genericTake n (repeat VarPatt) ++ qs) (shift n e)]
refine l n (Case (Tagged (Tag m ms _) ps : qs) e) | l == m =
  [Case (genericTake n (ps ++ repeat VarPatt) ++ qs) (shift (n - genericLength ps) e)]
refine l n (Case (Tagged (Tag m ms _) ps : qs) e) | otherwise =
  []

-- Extract the visit function

visit :: [Case] -> Exp -> [Exp] -> Exp
visit (Case (Tagged (Tag _ _ v) _ : _) _ : _ ) = v
visit (Case (VarPatt              : _) _ : cs) = visit cs
visit _                                        = Apply

-- Extract the list of possible tags, and their arity.

tags :: [Case] -> Map MemberId Nat
tags = foldl (unionWith max) empty . map tag

tag :: Case -> Map MemberId Nat
tag (Case (Tagged (Tag l ls _) ps : qs) e) =
  fromListWith max ((l, genericLength ps) : [ (l, 0) | l <- ls ])
tag _ = empty
