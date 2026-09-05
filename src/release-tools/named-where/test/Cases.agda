-- Test corpus for named-where.py.  This file is valid Agda.
-- The expected output of the tool is in `expected.txt`.

module Cases where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Equality

-- (1) An ordinary submodule declaration: NOT a named `where` module.
module Ordinary where
  ok : Nat
  ok = 0

-- (2) An ordinary submodule with parameters.
module Params (n : Nat) where
  ok : Nat
  ok = n

-- (3) A module in a `private` block: ordinary.
private
  module Priv where
    ok : Nat
    ok = 0

-- (4) A named `where` module, not under `with`/`rewrite`.
plain : Nat
plain = 0
  module P where
  q : Nat
  q = 1

-- (5) The same, after a right-hand side spanning several lines.
multi : Nat
multi = plain
          + 1
  module M2 where
  q : Nat
  q = 2

-- (6) Under `with`, `...` style.
w1 : Bool → Nat
w1 b with b
... | true  = 0
... | false = 1
  module W1 where
  q : Nat
  q = 3

-- (7) Under `with`, old style repeating the left-hand side.
w2 : Bool → Nat
w2 b with b
w2 b | true  = 0
w2 b | false = 1
  module W2 where
  q : Nat
  q = 4

-- (8) Under `rewrite`.
r1 : (n : Nat) → n ≡ 0 → n ≡ 0
r1 n e rewrite e = refl
  module R1 where
  q : Nat
  q = 5

-- (9) Under `with`, but nested inside an anonymous `where` block.
w3 : Bool → Nat
w3 b with b
... | true  = 0
... | false = aux
  where
  aux : Nat
  aux = 1
    module W3 where
    q : Nat
    q = 6

-- (10) `module _ where` is a named (`SomeWhere`) module for Agda.
anon : Nat
anon = 0
  module _ where
  q10 : Nat
  q10 = 7

-- (11) An ordinary module declaration inside a `where` block.
inWhere : Nat
inWhere = h
  where
  module Inner where
    k : Nat
    k = 0
  h : Nat
  h = Inner.k

-- (12) Comments and string literals must not confuse the scanner.
{- module Commented where
     still a comment {- nested -} -}
-- module LineCommented where
str : String
str = "module InString where"

-- (13) A `with` in a sibling definition must not leak.
after : Nat
after = 0
  module A13 where
  q : Nat
  q = 8

-- (14) A `let ... in` whose block is closed by indentation must not
-- confuse the layout tracker (regression: it used to drop the whole stack).
letIn : Nat
letIn = let x = 1
        in x

lastOne : Nat
lastOne = 0
  module L14 where
  q : Nat
  q = 9
