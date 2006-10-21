
module Logic.Relations where

import Logic.Base
import Data.Bool

Rel : Set -> Set1
Rel A = A -> A -> Set

Reflexive : {A : Set} -> Rel A -> Set
Reflexive {A} _R_ = (x : A) -> x R x

Symmetric : {A : Set} -> Rel A -> Set
Symmetric {A} _R_  = (x, y : A) -> x R y -> y R x

Transitive : {A : Set} -> Rel A -> Set
Transitive {A} _R_ = (x, y, z : A) -> x R y -> y R z -> x R z

module PolyEq (_≡_ : {A : Set} -> A -> A -> Set1) where

  Antisymmetric : {A : Set} -> Rel A -> Set1
  Antisymmetric {A} _R_ = (x, y : A) -> x R y -> y R x -> x ≡ y

module MonoEq {A : Set}(_≡_ : Rel A) where

  Antisymmetric : Rel A -> Set
  Antisymmetric _R_ = (x, y : A) -> x R y -> y R x -> x ≡ y

open Logic.Base

Total : {A : Set} -> Rel A -> Set
Total {A} _R_ = (x, y : A) -> (x R y) \/ (y R x)

Decidable : (P : Set) -> Set
Decidable P = P \/ ¬ P

