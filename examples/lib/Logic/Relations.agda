
module Logic.Relations where

import Logic.Base
import Data.Bool

Rel : Set -> Set1
Rel A = A -> A -> Set

Reflexive : {A : Set} -> Rel A -> Set
Reflexive {A} _R_ = (x : A) -> x R x

Symmetric : {A : Set} -> Rel A -> Set
Symmetric {A} _R_  = (x y : A) -> x R y -> y R x

Transitive : {A : Set} -> Rel A -> Set
Transitive {A} _R_ = (x y z : A) -> x R y -> y R z -> x R z

Congruent : {A : Set} -> Rel A -> Set
Congruent {A} _R_ = (f : A -> A)(x y : A) -> x R y -> f x R f y

Substitutive : {A : Set} -> Rel A -> Set1
Substitutive {A} _R_ = (P : A -> Set)(x y : A) -> x R y -> P x -> P y

module PolyEq (_≡_ : {A : Set} -> Rel A) where

  Antisymmetric : {A : Set} -> Rel A -> Set
  Antisymmetric {A} _R_ = (x y : A) -> x R y -> y R x -> x ≡ y

module MonoEq {A : Set}(_≡_ : Rel A) where

  Antisymmetric : Rel A -> Set
  Antisymmetric _R_ = (x y : A) -> x R y -> y R x -> x ≡ y

open Logic.Base

Total : {A : Set} -> Rel A -> Set
Total {A} _R_ = (x y : A) -> (x R y) \/ (y R x)

Decidable : (P : Set) -> Set
Decidable P = P \/ ¬ P

