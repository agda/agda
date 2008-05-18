
module Logic.Operations where

import Logic.Relations as Rel
import Logic.Equivalence as Eq
open Eq using (Equivalence; module Equivalence)

BinOp : Set -> Set
BinOp A = A -> A -> A

module MonoEq {A : Set}(Eq : Equivalence A) where

  module EqEq = Equivalence Eq
  open EqEq

  Commutative : BinOp A -> Set
  Commutative _+_ = (x y : A) -> (x + y) == (y + x)

  Associative : BinOp A -> Set
  Associative _+_ = (x y z : A) -> (x + (y + z)) == ((x + y) + z)

  LeftIdentity : A -> BinOp A -> Set
  LeftIdentity z _+_ = (x : A) -> (z + x) == x

  RightIdentity : A -> BinOp A -> Set
  RightIdentity z _+_ = (x : A) -> (x + z) == x

module Param where

  Commutative : {A : Set}(Eq : Equivalence A) -> BinOp A -> Set
  Commutative Eq = Op.Commutative
    where module Op = MonoEq Eq

  Associative : {A : Set}(Eq : Equivalence A) -> BinOp A -> Set
  Associative Eq = Op.Associative
    where module Op = MonoEq Eq

  LeftIdentity : {A : Set}(Eq : Equivalence A) -> A -> BinOp A -> Set
  LeftIdentity Eq = Op.LeftIdentity
    where module Op = MonoEq Eq

  RightIdentity : {A : Set}(Eq : Equivalence A) -> A -> BinOp A -> Set
  RightIdentity Eq = Op.RightIdentity
    where module Op = MonoEq Eq

