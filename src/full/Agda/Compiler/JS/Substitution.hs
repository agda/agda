module Agda.Compiler.JS.Substitution where

import Prelude hiding ( map, lookup )
import Data.Map ( empty, unionWith, singleton, findWithDefault )
import qualified Data.Map as Map
import Data.List ( genericIndex )
import qualified Data.List as List

import Agda.Syntax.Common ( Nat )
import Agda.Compiler.JS.Syntax
  ( Exp(Self,Undefined,Local,Lambda,Object,Array,Apply,Lookup,If,BinOp,PreOp),
    MemberId, LocalId(LocalId) )
import Agda.Utils.Function ( iterate' )
import Agda.Utils.List ( indexWithDefault )

-- Map for expressions

map :: Nat -> (Nat -> LocalId -> Exp) -> Exp -> Exp
map m f (Local i)       = f m i
map m f (Lambda i e)    = Lambda i (map (m + i) f e)
map m f (Object o)      = Object (Map.map (map m f) o)
map m f (Array es)      = Array (List.map (\(c, e) -> (c, map m f e)) es)
map m f (Apply e es)    = Apply (map m f e) (List.map (map m f) es)
map m f (Lookup e l)    = Lookup (map m f e) l
map m f (If e e' e'')   = If (map m f e) (map m f e') (map m f e'')
map m f (PreOp op e)    = PreOp op (map m f e)
map m f (BinOp e op e') = BinOp (map m f e) op (map m f e')
map m f e               = e

-- Shifting

shift :: Nat -> Exp -> Exp
shift = shiftFrom 0

shiftFrom :: Nat -> Nat -> Exp -> Exp
shiftFrom m 0 e = e
shiftFrom m n e = map m (shifter n) e

shifter :: Nat -> Nat -> LocalId -> Exp
shifter n m (LocalId i) | i < m     = Local (LocalId i)
shifter n m (LocalId i) | otherwise = Local (LocalId (i + n))

-- Substitution

subst :: Nat -> [Exp] -> Exp -> Exp
subst 0 es e = e
subst n es e = map 0 (substituter n es) e

substituter :: Nat -> [Exp] -> Nat -> LocalId -> Exp
substituter n es m (LocalId i) | i < m       = Local (LocalId i)
substituter n es m (LocalId i) | (i - m) < n = shift m (genericIndex (es ++ repeat Undefined) (n - (i + 1 - m)))
substituter n es m (LocalId i) | otherwise   = Local (LocalId (i - n))

-- A variant on substitution which performs beta-reduction

map' :: Nat -> (Nat -> LocalId -> Exp) -> Exp -> Exp
map' m f (Local i)       = f m i
map' m f (Lambda i e)    = Lambda i (map' (m + i) f e)
map' m f (Object o)      = Object (Map.map (map' m f) o)
map' m f (Array es)      = Array (List.map (\(c, e) -> (c, map' m f e)) es)
map' m f (Apply e es)    = apply (map' m f e) (List.map (map' m f) es)
map' m f (Lookup e l)    = lookup (map' m f e) l
map' m f (If e e' e'')   = If (map' m f e) (map' m f e') (map' m f e'')
map' m f (PreOp op e)    = PreOp op (map' m f e)
map' m f (BinOp e op e') = BinOp (map' m f e) op (map' m f e')
map' m f e               = e

subst' :: Nat -> [Exp] -> Exp -> Exp
subst' 0 es e = e
subst' n es e = map' 0 (substituter n es) e

-- Beta-reducing application and field access

apply :: Exp -> [Exp] -> Exp
apply (Lambda i e) es = subst' i es e
apply e            es = Apply e es

lookup :: Exp -> MemberId -> Exp
lookup (Object o) l = findWithDefault Undefined l o
lookup e          l = Lookup e l

-- Replace any top-level occurrences of self
-- (needed because JS is a cbv language, so any top-level
-- recursions would evaluate before the module has been defined,
-- e.g. exports = { x: 1, y: exports.x } results in an exception,
-- as exports is undefined at the point that exports.x is evaluated),

self :: Exp -> Exp -> Exp
self e (Self)         = e
self e (Object o)     = Object (Map.map (self e) o)
self e (Array es)     = Array (List.map (\(c, x) -> (c, self e x)) es)
self e (Apply f es)   = case (self e f) of
  (Lambda n g) -> self e (subst' n es g)
  g            -> Apply g (List.map (self e) es)
self e (Lookup f l)   = lookup (self e f) l
self e (If f g h)     = If (self e f) (self e g) (self e h)
self e (BinOp f op g) = BinOp (self e f) op (self e g)
self e (PreOp op f)   = PreOp op (self e f)
self e f              = f

-- Find the fixed point of an expression, with no top-level occurrences
-- of self.

fix :: Exp -> Exp
fix f = e where e = self e f

-- Some helper functions

curriedApply :: Exp -> [Exp] -> Exp
curriedApply = foldl (\ f e -> apply f [e])

curriedLambda :: Nat -> Exp -> Exp
curriedLambda n = iterate' n (Lambda 1)

emp :: Exp
emp = Object (empty)

union :: Exp -> Exp -> Exp
union (Object o) (Object p) = Object (unionWith union o p)
union e          f          = e

vine :: [MemberId] -> Exp -> Exp
vine ls e = foldr (\ l e -> Object (singleton l e)) e ls

object :: [([MemberId],Exp)] -> Exp
object = foldr (\ (ls,e) -> (union (vine ls e))) emp
