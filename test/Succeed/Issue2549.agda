{-# OPTIONS --cubical-compatible --rewriting --confluence-check #-}

postulate
  _↦_ : {A : Set} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}

data _==_ {A : Set} (a : A) : A → Set where
  idp : a == a

PathOver : {A : Set} (B : A → Set)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Set
PathOver B idp u v = (u == v)

infix 30 PathOver
syntax PathOver B p u v =
  u == v [ B ↓ p ]

apd : {A : Set} {B : A → Set} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → f x == f y [ B ↓ p ]
apd f idp = idp

module Disk where

module _ where

  postulate -- HIT
    Disk : Set
    baseD : Disk
    loopD : baseD == baseD
    drumD : loopD == idp

  module DiskElim {P : Disk → Set}
    (baseD* : P baseD )
    (loopD* : baseD* == baseD* [ P ↓ loopD ] )
    (drumD* : loopD* == idp [ ((λ p → baseD* == baseD* [ P ↓ p ] ) ) ↓ drumD ] ) where

    postulate
      f : (x : Disk) → P x
      baseD-β : f baseD ↦ baseD*
      {-# REWRITE baseD-β #-}

    postulate
      loopD-ι : apd f loopD ↦ loopD*
    {-# REWRITE loopD-ι #-}

    postulate
      drumD-ι : apd (apd f) drumD ↦ drumD*
    {-# REWRITE drumD-ι #-}

    loopD-β : apd f loopD == loopD*
    loopD-β = idp

    drumD-β : apd (apd f) drumD == drumD*
    drumD-β = idp
