{-# LANGUAGE CPP #-}

module Agda.Compiler.JS.Case where

import Prelude hiding ( null )
import Data.Map ( Map, empty, null, mapWithKey, fromListWith, unionWith )
import Data.List ( genericLength, genericTake, intercalate )

import Agda.Syntax.Common ( Nat )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

import Agda.Compiler.JS.Pretty ( Pretty, pretty, pretties )
import Agda.Compiler.JS.Syntax
  ( Exp(Undefined,Local,Lambda,Object,Apply,Lookup),
    LocalId(LocalId), MemberId )
import Agda.Compiler.JS.Substitution ( shiftFrom )

#include "../../undefined.h"

-- ECMAScript doesn't support pattern-mathching case, so
-- we translate to a visitor pattern.  We use a decision-tree
-- translation, as that seems to fit visitor objects better.

data Case = Case { pats :: [Patt], body :: Exp }
  deriving (Show)

instance Pretty Case where
  pretty n i (Case ps e) =
    intercalate " " (pretties n i ps) ++ " -> " ++ pretty (n + numVars ps) i e

-- Not handling literal patterns yet
-- Note that all patterns introduce binders, in depth-first prefix order,
-- for example Tagged l [ VarPatt , VarPatt ] should be thought
-- of as "x2 @ l (x1, x0)".

data Patt =
  VarPatt |
  Tagged Tag [Patt]
  deriving (Show)

instance Pretty Patt where
  pretty n i VarPatt = "x"
  pretty n i (Tagged (Tag l _ _) ps) =
    "(" ++ intercalate " " (pretty n i l : pretties n i ps) ++ ")"

-- With each tag, we record its name, and the names of the
-- other constructors of the datatype (e.g. we'd represent
-- zero as Tag "zero" ["suc","zero"]).  We also record the
-- the function which accepts a visitor (by default Apply,
-- but can be over-ridden by the FFI).

data Tag = Tag MemberId [MemberId] (Exp -> [Exp] ->  Exp)

instance Show Tag where
  show (Tag i is _) = show i

-- Number of bound variables in a pattern

numVars :: [Patt] -> Nat
numVars = sum . map numVars'

numVars' :: Patt -> Nat
numVars' (VarPatt)     = 1
numVars' (Tagged l ps) = 1 + numVars ps

-- Compile a case statement to a function
-- in lambda n cs, n is the number of parameters

lambda :: [Case] -> Exp
lambda []     = Undefined
lambda (c:cs) = lambda' 0 0 (genericLength (pats c)) (c:cs)

-- In lambda' l m n cs,
-- l is the number of free variables,
-- m is the number of already read parameters, with m <= l, and
-- n is the number of unread parameters.
-- Each case should be of the form (Case ps e) where ps has length m+n.
-- e can have (l - m + #bv ps) variables free.
-- lambda' l m n cs can have l variables free.

lambda' :: Nat -> Nat -> Nat -> [Case] -> Exp
lambda' l m n []       = Undefined
lambda' l 0 0 (c : cs) = body c
lambda' l 0 n cs       = Lambda 1 (lambda' (l+1) 1 (n-1) cs)
lambda' l m n cs       =
  case null ts of
    True -> lambda' l (m-1) n (map pop cs)
    False -> visit cs (Local (LocalId (m-1))) [Object (mapWithKey (match l (m-1) n cs) ts)]
  where
    ts = tags cs

-- Pop cases

pop :: Case -> Case
pop (Case (VarPatt : ps) e) = (Case ps e)
pop _                       = __IMPOSSIBLE__

-- Cases which match a given tag/arity

match :: Nat -> Nat -> Nat -> [Case] -> MemberId -> Nat -> Exp
match l m n cs t x = Lambda x (lambda' (l + x) (m + x) n (concat (map (refine t x) cs)))

-- Refine a case statement by a given tag/arity

refine :: MemberId -> Nat -> Case -> [Case]
refine t x (Case (VarPatt : qs) e) =
  [Case (genericTake x (repeat VarPatt) ++ qs) (shiftFrom (numVars qs) x e)]
refine t x (Case (Tagged (Tag u _ _) ps : qs) e) | t == u =
  [Case (ps ++ qs) e]
refine _ _ _ = []

-- Extract the visit function

visit :: [Case] -> Exp -> [Exp] -> Exp
visit (Case (Tagged (Tag _ _ v) _ : _) _ : _ ) = v
visit (Case (VarPatt              : _) _ : cs) = visit cs
visit _                                        = Apply

-- Extract the list of possible tags, and their arity.

tags :: [Case] -> Map MemberId Nat
tags = foldl (unionWith max) empty . map tag

tag :: Case -> Map MemberId Nat
tag (Case (Tagged (Tag t us _) ps : qs) e) =
  fromListWith max ((t, genericLength ps) : [ (u, 0) | u <- us ])
tag _ = empty
