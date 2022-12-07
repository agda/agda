-- Possible improvements:
-- * Parts of the code are not reachable from main.
-- * The following primitives are not used at all: primPOr, primComp,
--   primHComp, prim^glueU and prim^unglueU.

{-# OPTIONS --erased-cubical --erasure --save-metas #-}

-- The code from Agda.Builtin.Cubical.Glue should not be compiled.

open import Agda.Builtin.Cubical.Glue

open import Agda.Builtin.Cubical.HCompU
open import Agda.Builtin.Cubical.Id
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub
open import Agda.Builtin.IO
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Primitive.Cubical

open import Erased-cubical-Cubical

postulate
  putStr : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStr = Data.Text.IO.putStr #-}
{-# COMPILE JS putStr =
    function (x) {
      return function(cb) {
        process.stdout.write(x); cb(0); }; } #-}

i₁ : I
i₁ = primIMax (primIMax (primINeg i0) i1) (primIMin i1 i0)

i₁-1 : IsOne i₁
i₁-1 = IsOne1 (primIMax (primINeg i0) i1) (primIMin i1 i0)
         (IsOne2 (primINeg i0) i1 itIsOne)

p₁ : Partial i1 Nat
p₁ = λ _ → 12

p₂ : PartialP i1 (λ _ → Nat)
p₂ = λ _ → 12

p₃ : PartialP i0 (λ _ → Nat)
p₃ = isOneEmpty

p₄ : 12 ≡ 12
p₄ = λ _ → 12

n₁ : Nat
n₁ = p₄ i0

s : Sub Nat i1 (λ _ → 13)
s = inS 13

n₂ : Nat
n₂ = primSubOut s

i₂ : I
i₂ = primFaceForall (λ _ → i1)

i₃ : Id 12 12
i₃ = conid i0 p₄

i₄ : I
i₄ = primDepIMin i1 (λ _ → i0)

i₅ : I
i₅ = primIdFace i₃

p₅ : 12 ≡ 12
p₅ = primIdPath i₃

n₃ : Nat
n₃ = IdJ (λ _ _ → Nat) 14 i₃

n₄ : Nat
n₄ = primIdElim (λ _ _ → Nat) (λ _ _ _ → 14) i₃

infix 2 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- Some "standard" path functions.

refl : {A : Set} (x : A) → x ≡ x
refl x = λ _ → x

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym p i = p (primINeg i)

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f p i = f (p i)

J :
  {A : Set} {x y : A}
  (P : (x y : A) → x ≡ y → Set) →
  (∀ x → P x x (refl x)) →
  (x≡y : x ≡ y) → P x y x≡y
J {x = x} P p x≡y =
  primTransp (λ i → P _ _ (λ j → x≡y (primIMin i j))) i0 (p x)

subst :
  {A : Set} {x y : A}
  (P : A → Set) → x ≡ y → P x → P y
subst P eq p = primTransp (λ i → P (eq i)) i0 p

subst-refl :
  {A : Set} {x : A}
  (P : A → Set) {p : P x} →
  subst P (refl x) p ≡ p
subst-refl {x = x} P {p = p} i =
  primTransp (λ _ → P x) i p

-- The following definitions are perhaps less standard when paths are
-- used.

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans x≡y y≡z = subst (_ ≡_) y≡z x≡y

trans-refl-refl :
  {A : Set}
  (x : A) → trans (refl x) (refl x) ≡ refl x
trans-refl-refl x = subst-refl (x ≡_)

trans-sym :
  {A : Set} {x y : A} (x≡y : x ≡ y) →
  trans x≡y (sym x≡y) ≡ refl x
trans-sym =
  J (λ x y x≡y → trans x≡y (sym x≡y) ≡ refl x)
    trans-refl-refl

-- Propositions and sets.

Is-proposition : Set → Set
Is-proposition A = (x y : A) → x ≡ y

Is-set : Set → Set
Is-set A = (x y : A) → Is-proposition (x ≡ y)

-- Following Hedberg's "A coherence theorem for Martin-Löf's type
-- theory".

decidable-equality→is-set :
  {A : Set} →
  ((x y : A) → x ≡ y ⊎ (x ≡ y → ⊥)) →
  Is-set A
decidable-equality→is-set dec =
  constant⇒set (λ x y → decidable⇒constant (dec x y))
  where
  Constant : {A B : Set} → (A → B) → Set
  Constant f = ∀ x y → f x ≡ f y

  _Left-inverse-of_ : {A B : Set} → (B → A) → (A → B) → Set
  g Left-inverse-of f = ∀ x → g (f x) ≡ x

  proposition : {A : Set} →
                (f : Σ (A → A) Constant) →
                Σ _ (_Left-inverse-of (fst f)) →
                Is-proposition A
  proposition (f , constant) (g , left-inverse) x y =
    trans (sym (left-inverse x))
      (trans (cong g (constant x y)) (left-inverse y))

  left-inverse :
    {A : Set}
    (f : (x y : A) → x ≡ y → x ≡ y) →
    ∀ {x y} → Σ _ (_Left-inverse-of (f x y))
  left-inverse {A = A} f {x = x} {y = y} =
      (λ x≡y → trans x≡y (sym (f y y (refl y))))
    , J (λ x y x≡y → trans (f x y x≡y) (sym (f y y (refl y))) ≡ x≡y)
        (λ _ → trans-sym _)

  constant⇒set :
    {A : Set} →
    ((x y : A) → Σ (x ≡ y → x ≡ y) Constant) →
    Is-set A
  constant⇒set constant x y =
    proposition (constant x y)
                (left-inverse λ x y → fst (constant x y))

  decidable⇒constant :
    {A : Set} →
    A ⊎ (A → ⊥) →
    Σ (A → A) Constant
  decidable⇒constant (inj₁ x) =
    (λ _ → x) , (λ _ _ → refl x)
  decidable⇒constant (inj₂ ¬A) =
    (λ x → x) , (λ x → ⊥-elim (¬A x))

if_then_else_ : {A : Set₁} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

Bool-set : Is-set Bool
Bool-set = decidable-equality→is-set λ where
  false false → inj₁ λ _ → false
  true  true  → inj₁ λ _ → true
  false true  → inj₂ λ eq →
                  primTransp (λ i → if eq i then ⊥ else ⊤) i0 _
  true  false → inj₂ λ eq →
                  primTransp (λ i → if eq i then ⊤ else ⊥) i0 _

data ∥_∥ᴱ (A : Set) : Set where
  ∣_∣        : A → ∥ A ∥ᴱ
  @0 trivial : Is-proposition ∥ A ∥ᴱ

recᴱ : {A B : Set} → @0 Is-proposition B → (A → B) → ∥ A ∥ᴱ → B
recᴱ p f ∣ x ∣           = f x
recᴱ p f (trivial x y i) = p (recᴱ p f x) (recᴱ p f y) i

-- Following Vezzosi, Mörtberg and Abel's "Cubical Agda: A Dependently
-- Typed Programming Language with Univalence and Higher Inductive
-- Types".

data _/_ (A : Set) (R : A → A → Set) : Set where
  [_]                  : A → A / R
  []-respects-relation : (x y : A) → R x y → [ x ] ≡ [ y ]
  is-set               : Is-set (A / R)

rec :
  {A B : Set} {R : A → A → Set} →
  Is-set B →
  (f : A → B) →
  ((x y : A) → R x y → f x ≡ f y) →
  A / R → B
rec s f g [ x ]                          = f x
rec s f g ([]-respects-relation x y r i) = g x y r i
rec s f g (is-set x y p q i j)           =
  s (rec s f g x) (rec s f g y)
    (λ k → rec s f g (p k)) (λ k → rec s f g (q k)) i j

const-true : I → Bool
const-true i =
  rec
    {R = _≡_}
    Bool-set
    (λ x → x)
    (λ _ _ x≡y → x≡y)
    (is-set
       _ _
       ([]-respects-relation true true (refl true))
       (refl _)
       i i)

main : IO ⊤
main =
  putStr
    (recᴱ
       easy
       (λ where
          true  → "Success\n"
          false → "Failure\n")
       ∣ const-true i0 ∣)

-- It should be possible to mention things that are not compiled in
-- type signatures.

u₁ : Not-compiled → ⊤
u₁ _ = tt

@0 A : Set₁
A = Set

u₂ : A → ⊤
u₂ _ = tt
