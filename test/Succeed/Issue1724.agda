{-# OPTIONS --cubical-compatible --rewriting --confluence-check #-}

module _ where

{- Rewriting relation -}

postulate
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i
  idr : ∀ {i} {A : Set i} {a : A} → a ↦ a
{-# BUILTIN REWRITE _↦_ #-}

{- Identity type -}

infixr 3 _==_

data _==_ {i} {A : Set i} (a : A) : A → Set i where
  idp : a == a

ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
  → (p : x == y) → f x == f y
ap f idp = idp


postulate
  A : Set
  C : A → Set

-- Definition of W

postulate
  W : Set
  c : A → W

module _ {l} {P : W → Set l} (c* : (a : A) → P (c a)) where
  postulate
    W-elim : (w : W) → P w
    W-c-β : (a : A) → W-elim (c a) ↦ c* a
    {-# REWRITE W-c-β #-}

-- Definition of P

P : W → Set
P = W-elim C

-- Definition of WT

postulate
  WT : Set
  cT : (a : A) (x : C a) → WT

-- Definition of TotP

record TotP : Set where
  constructor _,_
  field
    fst : W
    snd : P fst

-- Function from TotP to WT

from-curry : (x : W) (y : P x) → WT
from-curry = W-elim cT

from : TotP → WT
from (x , y) = from-curry x y


postulate
  a : A
  x y : C a
  foo : (c a , x) == (c a , y)
  bar : cT a x == cT a y

  rew1 : ap from foo ↦ bar
{-# REWRITE rew1 #-}

-- The following has exactly the same type as [rew1], so [idr] should work
rew1' : ap from foo ↦ bar
rew1' = idr
