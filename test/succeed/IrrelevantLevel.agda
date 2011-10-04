{-# OPTIONS --experimental-irrelevance #-}
-- {-# OPTIONS -v tc.univ:100 -v tc.meta:100 #-}
--{-# OPTIONS -v tc.rec:100 #-}
-- Andreas, 2011-04-27 universe levels can be made irrelevant
-- Ulf 2011-10-03. No they can't. How is that even consistent?
-- Andreas, 2011-10-03. Yes, they can!
--   .(i : Level)(A : Set i)   does not mean that Set i = Set j for all i,j
-- but nl i A = nl j A  for all i,j.
module IrrelevantLevel where

-- open import Common.Level
postulate
  Level : Set
  lzero : Level
  lsuc  : (i : Level) → Level
  _⊔_   : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero  #-}
{-# BUILTIN LEVELSUC  lsuc   #-}
{-# BUILTIN LEVELMAX  _⊔_ #-}

infixl 6 _⊔_

postulate 
  Lst : .(i : Level)(A : Set i) -> Set i
  nl  : .(i : Level)(A : Set i) -> Lst i A
  cns : .(i : Level)(A : Set i) -> A -> Lst i A -> Lst i A


data List .(i : Level)(A : Set i) : Set i where
  nil  : List i A
  cons : A -> List i A -> List i A

singleton : .{i : Level}{A : Set i}(a : A) -> List i A
singleton a = cons a nil

record Wrap .(i : Level)(A : Set i) : Set i where
  field
    wrap : A

module M .(i : Level)(A : Set i) where

  data Li : Set i where
    ni : Li
    co : A -> Li -> Li

