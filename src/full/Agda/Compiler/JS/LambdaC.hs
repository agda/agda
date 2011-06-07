module Agda.Compiler.JS.LambdaC where

import Prelude hiding ( map )
import Data.Map ( Map, empty, toList, unionWith, singleton, findWithDefault )
import qualified Data.Map as M ( map )
import Data.List ( genericIndex )
import qualified Data.List as L ( map )

import Agda.Syntax.Common ( Nat )
import Agda.Utils.Function ( iterate' )

-- An untyped lambda calculus with records,
-- and a special self-binder for recursive declarations

data Exp =
  Self |
  Local LocalId |
  Global GlobalId |
  Undefined |
  String String |
  Char Char |
  Integer Integer |
  Double Double |
  Lambda Nat Exp |
  Object (Map MemberId Exp) |
  Apply Exp [Exp] |
  Lookup Exp MemberId
  deriving (Show)

-- Local identifiers are named by De Bruijn indices.
-- Global identifiers are named by string lists.
-- Object members are named by strings.

newtype LocalId = LocalId Nat
  deriving (Eq, Ord, Show)

newtype GlobalId = GlobalId [String]
  deriving (Eq, Ord, Show)

newtype MemberId = MemberId String
  deriving (Eq, Ord, Show)

-- The top-level compilation unit is a module, which names
-- the GId of its exports, and the GIds of its imports.

data Module = Module { modName :: GlobalId, imports :: [GlobalId], export :: Exp }
  deriving (Show)

-- Note that modules are allowed to be recursive,
-- since the exported GId may occur inside the exported expression

-- Map for expressions

map :: Nat -> (Nat -> LocalId -> Exp) -> Exp -> Exp
map m f (Local i)      = f m i
map m f (Lambda i e)   = Lambda i (map (m + i) f e)
map m f (Object o)     = Object (M.map (map m f) o)
map m f (Apply e es)   = Apply (map m f e) (L.map (map m f) es)
map m f (Lookup e l)   = Lookup (map m f e) l
map m f e              = e

-- Shifting

shift :: Nat -> Exp -> Exp
shift n = map 0 f where
  f :: Nat -> LocalId -> Exp
  f m (LocalId i) | i < m     = Local (LocalId i)
  f m (LocalId i) | otherwise = Local (LocalId (i + n))

-- Substitution

subst :: Nat -> [Exp] -> Exp -> Exp
subst n es = map 0 f where
  f :: Nat -> LocalId -> Exp
  f m (LocalId i) | i < m       = Local (LocalId i)
  f m (LocalId i) | (i - m) < n = shift m (genericIndex (es ++ repeat Undefined) (i - m))
  f m (LocalId i) | otherwise   = Local (LocalId (i - n))

-- Replace any top-level occurrences of self
-- (needed because JS is a cbv language, so any top-level
-- recursions would evaluate before the module has been defined,
-- e.g. exports = { x: 1, y: exports.x } results in an exception,
-- as exports is undefined at the point that exports.x is evaluated),

self :: Exp -> Exp -> Exp
self e (Self)       = e
self e (Object o)   = Object (M.map (self e) o)
self e (Apply f es) = case self e f of
  Lambda n g -> self e (subst n es g)
  g          -> Apply g (L.map (self e) es)
self e (Lookup f l) = case self e f of
  Object o   -> findWithDefault Undefined l o
  g          -> Lookup g l
self e f             = f

-- Find the fixed point of an expression, with no top-level occurrences
-- of self.

fix :: Exp -> Exp
fix f = e where e = self e f

-- Some helper functions

curriedApply :: Exp -> [Exp] -> Exp
curriedApply = foldl (\ f e -> Apply f [e])

curriedLambda :: Nat -> Exp -> Exp
curriedLambda n = iterate' n (Lambda 1)

emp :: Exp
emp = Object (empty)

union :: Exp -> Exp -> Exp
union (Object o) (Object p) = Object (unionWith union o p)
union e          f          = e

vine :: [MemberId] -> Exp -> Exp
vine ls e = foldr (\ l e -> Object (singleton l e)) e ls

record :: [([MemberId],Exp)] -> Exp
record = foldr (\ (ls,e) -> (union (vine ls e))) emp
