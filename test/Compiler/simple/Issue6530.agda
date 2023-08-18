{-# OPTIONS --erased-cubical --erasure --no-main #-}
module Issue6530 where

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Primitive
open import Agda.Primitive.Cubical

private variable
  a b ℓ : Level
  A : Set a
  x y : A
  B : A → Set b

is-of-hlevel : Nat → Set ℓ → Set ℓ
is-of-hlevel 0 A = Σ A λ x → ∀ y → x ≡ y
is-of-hlevel 1 A = (x y : A) → x ≡ y
is-of-hlevel (suc (suc h)) A = (x y : A) → is-of-hlevel (suc h) (x ≡ y)

transport : {A B : Set ℓ} → A ≡ B → A → B
transport p a = primTransp (λ i → p i) i0 a

to-pathP : {A : I → Set ℓ} {x : A i0} {y : A i1} → transport (λ i → A i) x ≡ y → PathP A x y
to-pathP {A = A} {x} p i = primHComp (λ j → λ { (i = i0) → x
                                              ; (i = i1) → p j })
                          (primTransp (λ j → A (primIMin i j)) (primINeg i) x)

J : (P : ∀ y → x ≡ y → Set ℓ) (d : P x (λ _ → x)) (p : x ≡ y) → P y p
J P d p = transport (λ i → P (p i) (λ j → p (primIMin i j))) d

is-prop→pathP : {B : I → Set ℓ}
                (h : (i : I) → is-of-hlevel 1 (B i))
              → (b₀ : B i0) (b₁ : B i1)
              → PathP B b₀ b₁
is-prop→pathP h b₀ b₁ = to-pathP (h i1 _ b₁)

is-of-hlevel-dep : Nat → (A → Set ℓ) → Set _
is-of-hlevel-dep 0 B =
  ∀ {x y} (α : B x) (β : B y) (p : x ≡ y) → PathP (λ i → B (p i)) α β
is-of-hlevel-dep (suc n) B =
  ∀ {a₀ a₁} (b₀ : B a₀) (b₁ : B a₁)
  → is-of-hlevel-dep {A = a₀ ≡ a₁} n (λ p → PathP (λ i → B (p i)) b₀ b₁)

is-of-hlevel→is-of-hlevel-dep
  : (n : Nat) (hl : ((x : A) → is-of-hlevel (suc n) (B x)))
  → is-of-hlevel-dep n B
is-of-hlevel→is-of-hlevel-dep 0 hl α β p = is-prop→pathP (λ i → hl (p i)) α β
is-of-hlevel→is-of-hlevel-dep {A = A} {B = B} (suc n) hl {a₀} {a₁} b₀ b₁ =
  is-of-hlevel→is-of-hlevel-dep n λ p →
    J (λ a₁ p → ∀ b₁ → is-of-hlevel (suc n) (PathP (λ i → B (p i)) b₀ b₁))
    (hl a₀ b₀) p b₁
