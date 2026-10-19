-- Andreas, 2025-12-05, issue #8263
-- Shrunk from https://github.com/HoTT-Intro/Agda
-- Internal error in ProjectionLike, regression in 2.6.4
-- Culprit may have been b6c76f409c294691c33112f9144ef2393a335cfe

{-# OPTIONS --without-K #-}

-- {-# OPTIONS -v tc.infer:40 #-}

module _ where

open import Agda.Primitive
open import Agda.Builtin.Equality renaming (_≡_ to Id)
open import Agda.Builtin.Nat renaming (Nat to ℕ)


tr :
  {i j : Level} {A : Set i} (B : A → Set j) {x y : A} (p : Id x y) → B x → B y
tr B refl b = b

data Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  pair : (x : A) → (B x → Σ A B)

pr1 : {l1 l2 : Level} {A : Set l1} {B : A → Set l2} → Σ A B → A
pr1 (pair a _) = a

pr2 : {l1 l2 : Level} {A : Set l1} {B : A → Set l2} → (t : Σ A B) → B (pr1 t)
pr2 (pair a b) = b

_×_ : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
_×_ = λ A B → Σ A (λ _ → B)

is-contr :
  {l : Level} → Set l → Set l
is-contr A = Σ A (λ a → (x : A) → Id a x)

is-prop :
  {i : Level} (A : Set i) → Set i
is-prop A = (x y : A) → is-contr (Id x y)

UU-Prop :
  (l : Level) → Set (lsuc l)
UU-Prop l = Σ (Set l) is-prop

all-elements-equal :
  {i : Level} (A : Set i) → Set i
all-elements-equal A = (x y : A) → Id x y

postulate
  type-trunc-Prop : {l : Level} → Set l → Set l

  is-prop-all-elements-equal :
    {i : Level} {A : Set i} → all-elements-equal A → is-prop A

  is-prop-type-trunc-Prop : {l : Level} {A : Set l} → is-prop (type-trunc-Prop A)

trunc-Prop : {l : Level} → Set l → UU-Prop l
trunc-Prop A = pair (type-trunc-Prop A) is-prop-type-trunc-Prop

postulate
  mere-equiv-Prop :
    {l1 l2 : Level} → Set l1 → Set l2 → UU-Prop (l1 ⊔ l2)

mere-equiv :
  {l1 l2 : Level} → Set l1 → Set l2 → Set (l1 ⊔ l2)
mere-equiv X Y = pr1 (mere-equiv-Prop X Y)

data unit : Set where
  star : unit

data empty : Set where

data coprod {l1 l2 : Level} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2)  where
  inl : A → coprod A B
  inr : B → coprod A B

Fin : ℕ → Set
Fin zero = empty
Fin (suc k) = coprod (Fin k) unit

UU-Fin : ℕ → Set1
UU-Fin k =  Σ Set (mere-equiv (Fin k))

_~_ :
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2}
  (f g : (x : A) → B x) → Set (l1 ⊔ l2)
f ~ g = (x : _) → Id (f x) (g x)

id : {i : Level} {A : Set i} → A → A
id a = a

_∘_ :
  {i j k : Level} {A : Set i} {B : Set j} {C : Set k} →
  (B → C) → ((A → B) → (A → C))
(g ∘ f) a = g (f a)

sec :
  {i j : Level} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
sec {i} {j} {A} {B} f = Σ (B → A) (λ g → (f ∘ g) ~ id)

retr :
  {i j : Level} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
retr {i} {j} {A} {B} f = Σ (B → A) (λ g → (g ∘ f) ~ id)

is-equiv :
  {i j : Level} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
is-equiv f = sec f × retr f

_≃_ :
  {i j : Level} (A : Set i) (B : Set j) → Set (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → is-equiv f)

postulate
  is-contr-total-Eq-Π :
    ∀ { l1 l2 l3} {A : Set l1} {B : A → Set l2} (C : (x : A) → B x → Set l3) →
    ( is-contr-total-C : (x : A) → is-contr (Σ (B x) (C x))) →
    is-contr (Σ ((x : A) → B x) (λ g → (x : A) → C x (g x)))

  is-contr-total-Eq-structure :
    ∀ { l1 l2 l3 l4 : Level} { A : Set l1} {B : A → Set l2} {C : A → Set l3}
    ( D : (x : A) → B x → C x → Set l4) →
    ( is-contr-AC : is-contr (Σ A C)) →
    ( t : Σ A C) →
    is-contr (Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
    is-contr (Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))))

cube : ℕ → Set₁
cube k = Σ (UU-Fin k) (λ X → pr1 X → UU-Fin 2)

equiv-cube : {k : ℕ} → cube k → cube k → Set
equiv-cube {k} X Y =
  Σ ( (pr1 (pr1 X)) ≃ (pr1 (pr1 Y)))
    ( λ e → (x : pr1 (pr1 X))
          → (pr1 (pr2 X x)) ≃ ( pr1 (pr2 Y (pr1 e x))))

htpy-equiv-cube :
  {k : ℕ} (X Y : cube k) (e f : equiv-cube X Y) → Set
htpy-equiv-cube X Y e f =
  Σ ( pr1 (pr1 e) ~ pr1 (pr1 f))
    ( λ H → (d : pr1 (pr1 X)) →
            ( tr (pr1 ∘ pr2 Y) (H d) ∘ pr1 (pr2 e d))
            ~
            ( pr1 (pr2 f d)))
postulate
  is-contr-total-htpy-equiv : {l1 l2 : Level} {A : Set l1} {B : Set l2}
    (e : A ≃ B) → is-contr (Σ (A ≃ B) (λ e' → (pr1 e) ~ (pr1 e')))

-- Internal error:
is-contr-total-htpy-equiv-cube :
  {k : ℕ} (X Y : cube k) (e : equiv-cube X Y) →
  is-contr (Σ (equiv-cube X Y) (htpy-equiv-cube X Y e))
is-contr-total-htpy-equiv-cube X Y e =
  is-contr-total-Eq-structure
    ( λ α β H →
      ( d : pr1 (pr1 X)) →
      ( λ bar → tr (λ foo → pr1 (pr2 Y foo)) (H d) (pr1 (pr2 e d) bar))
      ~
      ( pr1 (β d))
    )
    ( is-contr-total-htpy-equiv (pr1 e))
    ( pair (pr1 e) (λ _ → refl))
    ( is-contr-total-Eq-Π
      ( λ d β → pr1 (pr2 e d) ~ pr1 β)
      ( λ d → is-contr-total-htpy-equiv (pr2 e d))
    )

-- Error was:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: __IMPOSSIBLE__, called at
-- src/full/Agda/TypeChecking/ProjectionLike.hs:466:54

-- Should succeed
