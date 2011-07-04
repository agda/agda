module RecordPatternMatching where

-- Sigma type.

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

-- Curry and uncurry with pattern matching.

curry : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

-- We still have η-equality.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

curry∘uncurry : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set} →
                (f : (x : A) → (y : B x) → C (x , y)) →
                (x : A) → (y : B x) →
                curry {C = C} (uncurry f) x y ≡ f x y
curry∘uncurry f x y = refl

uncurry∘curry : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set} →
                (f : (p : Σ A B) → C p) →
                (p : Σ A B) →
                uncurry {C = C} (curry f) p ≡ f p
uncurry∘curry f p = refl

-- Nested pattern matching is also possible.

to : {A B C : Set} → A × (B × C) → (A × B) × C
to (x , (y , z)) = ((x , y) , z)

from : {A B C : Set} → (A × B) × C → A × (B × C)
from ((x , y) , z) = (x , (y , z))

from∘to : {A B C : Set} (p : A × (B × C)) → from (to p) ≡ p
from∘to p = refl

data Bool : Set where
  true false : Bool

data ⊥ : Set where

F : Bool → Set
F true  = Bool
F false = ⊥

foo : Σ Bool F → Bool
foo (true  , b)  = b
foo (false , ())

bar : ∀ p → F (foo p) → F (foo p)
bar (true  , true)  = λ b → b
bar (true  , false) = λ ()
bar (false , ())

baz : (Σ Bool λ _ → Σ Bool λ _ → Bool) → Bool
baz (true  , (b , c)) = b
baz (false , (b , c)) = c

lemma : ∀ p → baz (false , p) ≡ proj₂ p
lemma p = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

add : ℕ × ℕ → ℕ
add (zero  , n) = n
add (suc m , n) = suc (add (m , n))

-- The code below used to trigger a bug: in one part of the code B was
-- assumed to be reduced to an application of a record type
-- constructor.

data Unit : Set where
  unit : Unit

B : Set
B = Σ Unit λ _ → Unit

C : B → Set₁
C (_ , _) = Set

-- The code below, which involves a clause with a "swapping
-- permutation", also used to trigger a bug.

data P : ⊥ → ⊥ → Set where
  p : (x y : ⊥) → P x y

Bar : (x : ⊥) → P x x → P x x → Set₁
Bar .x _ (p x .x) = Set

-- Another example which used to trigger a bug:

G : (Σ ⊥ λ x → Σ ⊥ λ y → x ≡ y) → Set₁
G (x , (.x , refl)) = Set

-- Record patterns containing dot patterns are supported.

Foo : (p₁ p₂ : B) → proj₁ p₁ ≡ proj₁ p₂ → Unit
Foo (x , y) (.x , y′) refl = unit

Foo-eval : (p : B) → Foo p p refl ≡ unit
Foo-eval _ = refl

-- Record patterns containing dot patterns as well as data type
-- patterns are also supported.

D : (p₁ p₂ : B) → proj₁ p₁ ≡ proj₁ p₂ → Set₁
D (x , y) (.x , unit) refl = Set
