------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to addition of integers
------------------------------------------------------------------------

module Data.Integer.Addition.Properties where

open import Algebra
open import Algebra.Structures
open import Data.Integer hiding (suc)
open import Data.Nat.Base using (suc; zero) renaming (_+_ to _ℕ+_)
import Data.Nat.Properties as ℕ
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties (_≡_ {A = ℤ})

------------------------------------------------------------------------
-- Addition and zero form a commutative monoid

comm : Commutative _+_
comm -[1+ a ] -[1+ b ] rewrite ℕ.+-comm a b = refl
comm (+   a ) (+   b ) rewrite ℕ.+-comm a b = refl
comm -[1+ _ ] (+   _ ) = refl
comm (+   _ ) -[1+ _ ] = refl

identityˡ : LeftIdentity (+ 0) _+_
identityˡ -[1+ _ ] = refl
identityˡ (+   _ ) = refl

identityʳ : RightIdentity (+ 0) _+_
identityʳ x rewrite comm x (+ 0) = identityˡ x

distribˡ-⊖-+-neg : ∀ a b c → b ⊖ c + -[1+ a ] ≡ b ⊖ (suc c ℕ+ a)
distribˡ-⊖-+-neg _ zero    zero    = refl
distribˡ-⊖-+-neg _ zero    (suc _) = refl
distribˡ-⊖-+-neg _ (suc _) zero    = refl
distribˡ-⊖-+-neg a (suc b) (suc c) = distribˡ-⊖-+-neg a b c

distribʳ-⊖-+-neg : ∀ a b c → -[1+ a ] + (b ⊖ c) ≡ b ⊖ (suc a ℕ+ c)
distribʳ-⊖-+-neg a b c
  rewrite comm -[1+ a ] (b ⊖ c)
        | distribˡ-⊖-+-neg a b c
        | ℕ.+-comm a c
        = refl

distribˡ-⊖-+-pos : ∀ a b c → b ⊖ c + + a ≡ b ℕ+ a ⊖ c
distribˡ-⊖-+-pos _ zero    zero    = refl
distribˡ-⊖-+-pos _ zero    (suc _) = refl
distribˡ-⊖-+-pos _ (suc _) zero    = refl
distribˡ-⊖-+-pos a (suc b) (suc c) = distribˡ-⊖-+-pos a b c

distribʳ-⊖-+-pos : ∀ a b c → + a + (b ⊖ c) ≡ a ℕ+ b ⊖ c
distribʳ-⊖-+-pos a b c
  rewrite comm (+ a) (b ⊖ c)
        | distribˡ-⊖-+-pos a b c
        | ℕ.+-comm a b
        = refl

assoc : Associative _+_
assoc (+ zero) y z rewrite identityˡ      y  | identityˡ (y + z) = refl
assoc x (+ zero) z rewrite identityʳ  x      | identityˡ      z  = refl
assoc x y (+ zero) rewrite identityʳ (x + y) | identityʳ  y      = refl
assoc -[1+ a ]  -[1+ b ]  (+ suc c) = sym (distribʳ-⊖-+-neg a c b)
assoc -[1+ a ]  (+ suc b) (+ suc c) = distribˡ-⊖-+-pos (suc c) b a
assoc (+ suc a) -[1+ b ]  -[1+ c ]  = distribˡ-⊖-+-neg c a b
assoc (+ suc a) -[1+ b ] (+ suc c)
  rewrite distribˡ-⊖-+-pos (suc c) a b
        | distribʳ-⊖-+-pos (suc a) c b
        | sym (ℕ.+-assoc a 1 c)
        | ℕ.+-comm a 1
        = refl
assoc (+ suc a) (+ suc b) -[1+ c ]
  rewrite distribʳ-⊖-+-pos (suc a) b c
        | sym (ℕ.+-assoc a 1 b)
        | ℕ.+-comm a 1
        = refl
assoc -[1+ a ] -[1+ b ] -[1+ c ]
  rewrite sym (ℕ.+-assoc a 1 (b ℕ+ c))
        | ℕ.+-comm a 1
        | ℕ.+-assoc a b c
        = refl
assoc -[1+ a ] (+ suc b) -[1+ c ]
  rewrite distribʳ-⊖-+-neg a b c
        | distribˡ-⊖-+-neg c b a
        = refl
assoc (+ suc a) (+ suc b) (+ suc c)
  rewrite ℕ.+-assoc (suc a) (suc b) (suc c)
        = refl

isSemigroup : IsSemigroup _≡_ _+_
isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = assoc
  ; ∙-cong        = cong₂ _+_
  }

isCommutativeMonoid : IsCommutativeMonoid _≡_ _+_ (+ 0)
isCommutativeMonoid = record
  { isSemigroup = isSemigroup
  ; identityˡ   = identityˡ
  ; comm        = comm
  }

commutativeMonoid : CommutativeMonoid _ _
commutativeMonoid = record
  { Carrier             = ℤ
  ; _≈_                 = _≡_
  ; _∙_                 = _+_
  ; ε                   = + 0
  ; isCommutativeMonoid = isCommutativeMonoid
  }
