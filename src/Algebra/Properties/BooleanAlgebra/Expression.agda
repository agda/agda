------------------------------------------------------------------------
-- The Agda standard library
--
-- Boolean algebra expressions
------------------------------------------------------------------------

open import Algebra

module Algebra.Properties.BooleanAlgebra.Expression
  {b} (B : BooleanAlgebra b b)
  where

open BooleanAlgebra B

open import Category.Applicative
import Category.Applicative.Indexed as Applicative
open import Category.Monad
open import Category.Monad.Identity
open import Data.Fin using (Fin)
open import Data.Nat
open import Data.Vec as Vec using (Vec)
open import Data.Product using (_,_; proj₁; proj₂)
import Data.Vec.Properties as VecProp
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≗_)
import Relation.Binary.Reflection as Reflection
open import Relation.Binary.Vec.Pointwise as PW
  using (Pointwise; module Pointwise; ext)

-- Expressions made up of variables and the operations of a boolean
-- algebra.

infixr 7 _and_
infixr 6 _or_

data Expr n : Set b where
  var        : (x : Fin n) → Expr n
  _or_ _and_ : (e₁ e₂ : Expr n) → Expr n
  not        : (e : Expr n) → Expr n
  top bot    : Expr n

-- The semantics of an expression, parametrised by an applicative
-- functor.

module Semantics
  {F : Set b → Set b}
  (A : RawApplicative F)
  where

  open RawApplicative A

  ⟦_⟧ : ∀ {n} → Expr n → Vec (F Carrier) n → F Carrier
  ⟦ var x     ⟧ ρ = Vec.lookup x ρ
  ⟦ e₁ or e₂  ⟧ ρ = pure _∨_ ⊛ ⟦ e₁ ⟧ ρ ⊛ ⟦ e₂ ⟧ ρ
  ⟦ e₁ and e₂ ⟧ ρ = pure _∧_ ⊛ ⟦ e₁ ⟧ ρ ⊛ ⟦ e₂ ⟧ ρ
  ⟦ not e     ⟧ ρ = pure ¬_ ⊛ ⟦ e ⟧ ρ
  ⟦ top       ⟧ ρ = pure ⊤
  ⟦ bot       ⟧ ρ = pure ⊥

-- flip Semantics.⟦_⟧ e is natural.

module Naturality
  {F₁ F₂ : Set b → Set b}
  {A₁ : RawApplicative F₁}
  {A₂ : RawApplicative F₂}
  (f : Applicative.Morphism A₁ A₂)
  where

  open P.≡-Reasoning
  open Applicative.Morphism f
  open Semantics A₁ renaming (⟦_⟧ to ⟦_⟧₁)
  open Semantics A₂ renaming (⟦_⟧ to ⟦_⟧₂)
  open RawApplicative A₁ renaming (pure to pure₁; _⊛_ to _⊛₁_)
  open RawApplicative A₂ renaming (pure to pure₂; _⊛_ to _⊛₂_)

  natural : ∀ {n} (e : Expr n) → op ∘ ⟦ e ⟧₁ ≗ ⟦ e ⟧₂ ∘ Vec.map op
  natural (var x) ρ = begin
    op (Vec.lookup x ρ)                                            ≡⟨ P.sym $ VecProp.lookup-map x op ρ ⟩
    Vec.lookup x (Vec.map op ρ)                                    ∎
  natural (e₁ or e₂) ρ = begin
    op (pure₁ _∨_ ⊛₁ ⟦ e₁ ⟧₁ ρ ⊛₁ ⟦ e₂ ⟧₁ ρ)                       ≡⟨ op-⊛ _ _ ⟩
    op (pure₁ _∨_ ⊛₁ ⟦ e₁ ⟧₁ ρ) ⊛₂ op (⟦ e₂ ⟧₁ ρ)                  ≡⟨ P.cong₂ _⊛₂_ (op-⊛ _ _) P.refl ⟩
    op (pure₁ _∨_) ⊛₂ op (⟦ e₁ ⟧₁ ρ) ⊛₂ op (⟦ e₂ ⟧₁ ρ)             ≡⟨ P.cong₂ _⊛₂_ (P.cong₂ _⊛₂_ (op-pure _) (natural e₁ ρ))
                                                                                   (natural e₂ ρ) ⟩
    pure₂ _∨_ ⊛₂ ⟦ e₁ ⟧₂ (Vec.map op ρ) ⊛₂ ⟦ e₂ ⟧₂ (Vec.map op ρ)  ∎
  natural (e₁ and e₂) ρ = begin
    op (pure₁ _∧_ ⊛₁ ⟦ e₁ ⟧₁ ρ ⊛₁ ⟦ e₂ ⟧₁ ρ)                       ≡⟨ op-⊛ _ _ ⟩
    op (pure₁ _∧_ ⊛₁ ⟦ e₁ ⟧₁ ρ) ⊛₂ op (⟦ e₂ ⟧₁ ρ)                  ≡⟨ P.cong₂ _⊛₂_ (op-⊛ _ _) P.refl ⟩
    op (pure₁ _∧_) ⊛₂ op (⟦ e₁ ⟧₁ ρ) ⊛₂ op (⟦ e₂ ⟧₁ ρ)             ≡⟨ P.cong₂ _⊛₂_ (P.cong₂ _⊛₂_ (op-pure _) (natural e₁ ρ))
                                                                                   (natural e₂ ρ) ⟩
    pure₂ _∧_ ⊛₂ ⟦ e₁ ⟧₂ (Vec.map op ρ) ⊛₂ ⟦ e₂ ⟧₂ (Vec.map op ρ)  ∎
  natural (not e) ρ = begin
    op (pure₁ ¬_ ⊛₁ ⟦ e ⟧₁ ρ)                                      ≡⟨ op-⊛ _ _ ⟩
    op (pure₁ ¬_) ⊛₂ op (⟦ e ⟧₁ ρ)                                 ≡⟨ P.cong₂ _⊛₂_ (op-pure _) (natural e ρ) ⟩
    pure₂ ¬_ ⊛₂ ⟦ e ⟧₂ (Vec.map op ρ)                              ∎
  natural top ρ = begin
    op (pure₁ ⊤)                                                   ≡⟨ op-pure _ ⟩
    pure₂ ⊤                                                        ∎
  natural bot ρ = begin
    op (pure₁ ⊥)                                                   ≡⟨ op-pure _ ⟩
    pure₂ ⊥                                                        ∎

-- An example of how naturality can be used: Any boolean algebra can
-- be lifted, in a pointwise manner, to vectors of carrier elements.

lift : ℕ → BooleanAlgebra b b
lift n = record
  { Carrier          = Vec Carrier n
  ; _≈_              = Pointwise _≈_
  ; _∨_              = zipWith _∨_
  ; _∧_              = zipWith _∧_
  ; ¬_               = map ¬_
  ; ⊤                = pure ⊤
  ; ⊥                = pure ⊥
  ; isBooleanAlgebra = record
    { isDistributiveLattice = record
      { isLattice = record
        { isEquivalence = PW.isEquivalence isEquivalence
        ; ∨-comm        = λ _ _ → ext λ i →
                            solve i 2 (λ x y → x or y , y or x)
                                  (∨-comm _ _) _ _
        ; ∨-assoc       = λ _ _ _ → ext λ i →
                            solve i 3
                              (λ x y z → (x or y) or z , x or (y or z))
                              (∨-assoc _ _ _) _ _ _
        ; ∨-cong        = λ xs≈us ys≈vs → ext λ i →
                            solve₁ i 4 (λ x y u v → x or y , u or v)
                                   _ _ _ _
                                   (∨-cong (Pointwise.app xs≈us i)
                                           (Pointwise.app ys≈vs i))
        ; ∧-comm        = λ _ _ → ext λ i →
                            solve i 2 (λ x y → x and y , y and x)
                                  (∧-comm _ _) _ _
        ; ∧-assoc       = λ _ _ _ → ext λ i →
                            solve i 3
                              (λ x y z → (x and y) and z ,
                                         x and (y and z))
                              (∧-assoc _ _ _) _ _ _
        ; ∧-cong        = λ xs≈ys us≈vs → ext λ i →
                            solve₁ i 4 (λ x y u v → x and y , u and v)
                                   _ _ _ _
                                   (∧-cong (Pointwise.app xs≈ys i)
                                           (Pointwise.app us≈vs i))
        ; absorptive    = (λ _ _ → ext λ i →
                             solve i 2 (λ x y → x or (x and y) , x)
                                   (proj₁ absorptive _ _) _ _) ,
                          (λ _ _ → ext λ i →
                             solve i 2 (λ x y → x and (x or y) , x)
                                   (proj₂ absorptive _ _) _ _)
        }
      ; ∨-∧-distribʳ = λ _ _ _ → ext λ i →
                         solve i 3
                               (λ x y z → (y and z) or x ,
                                          (y or x) and (z or x))
                               (∨-∧-distribʳ _ _ _) _ _ _
      }
    ; ∨-complementʳ = λ _ → ext λ i →
                        solve i 1 (λ x → x or (not x) , top)
                              (∨-complementʳ _) _
    ; ∧-complementʳ = λ _ → ext λ i →
                        solve i 1 (λ x → x and (not x) , bot)
                              (∧-complementʳ _) _
    ; ¬-cong        = λ xs≈ys → ext λ i →
                        solve₁ i 2 (λ x y → not x , not y) _ _
                               (¬-cong (Pointwise.app xs≈ys i))
    }
  }
  where
  open RawApplicative Vec.applicative
    using (pure; zipWith) renaming (_<$>_ to map)

  ⟦_⟧Id : ∀ {n} → Expr n → Vec Carrier n → Carrier
  ⟦_⟧Id = Semantics.⟦_⟧ (RawMonad.rawIApplicative IdentityMonad)

  ⟦_⟧Vec : ∀ {m n} → Expr n → Vec (Vec Carrier m) n → Vec Carrier m
  ⟦_⟧Vec = Semantics.⟦_⟧ Vec.applicative

  open module R {n} (i : Fin n) =
    Reflection setoid var
      (λ e ρ → Vec.lookup i (⟦ e ⟧Vec ρ))
      (λ e ρ → ⟦ e ⟧Id (Vec.map (Vec.lookup i) ρ))
      (λ e ρ → sym $ reflexive $
                 Naturality.natural (VecProp.lookup-morphism i) e ρ)
