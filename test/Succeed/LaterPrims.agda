{-# OPTIONS --cubical --guarded #-}
module LaterPrims where

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private
  variable
    l : Level
    A B : Set l

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) -> A

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

transpLater : ∀ (A : I → ▹ Set) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 a = primTransp (\ i → A i a) i0 (u0 a)

transpLater-prim : (A : I → ▹ Set) → (x : ▸ (A i0)) → ▸ (A i1)
transpLater-prim A x = primTransp (\ i → ▸ (A i)) i0 x

transpLater-test : ∀ (A : I → ▹ Set) → (x : ▸ (A i0)) → transpLater-prim A x ≡ transpLater A x
transpLater-test A x = \ _ → transpLater-prim A x


hcompLater-prim : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater-prim A φ u u0 a = primHComp (\ { i (φ = i1) → u i 1=1 a }) (outS u0 a)


hcompLater : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 = primHComp (\ { i (φ = i1) → u i 1=1 }) (outS u0)

hcompLater-test : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → hcompLater A φ u u0 ≡ hcompLater-prim A φ u u0
hcompLater-test A φ u x = \ _ → hcompLater-prim A φ u x

ap : ∀ {A B : Set} (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
ap f eq = \ i → f (eq i)

_$>_ : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ x → f x ≡ g x
eq $> x = \ i → eq i x
later-ext : ∀ {A : Set} → {f g : ▹ A} → (▸ \ α → f α ≡ g α) → f ≡ g
later-ext eq = \ i α → eq α i

postulate
  dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
  pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ (\ _ → f (dfix f))

pfix' : ∀ {l} {A : Set l} (f : ▹ A → A) → ▸ \ α → dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : ∀ {l} {A : Set l} → (▹ A → A) → A
fix f = f (dfix f)

data gStream (A : Set) : Set where
  cons : (x : A) (xs : ▹ gStream A) → gStream A


repeat : ∀ {A : Set} → A → gStream A
repeat a = fix \ repeat▹ → cons a repeat▹

repeat-eq : ∀ {A : Set} (a : A) → repeat a ≡ cons a (\ α → repeat a)
repeat-eq a = ap (cons a) (pfix (cons a))

map : ∀ {A B : Set} → (A → B) → gStream A → gStream B
map f = fix \ map▹ → \ { (cons a as) → cons (f a) \ α → map▹ α (as α) }

map-eq : ∀ {A B : Set} → (f : A → B) → ∀ a as → map f (cons a as) ≡ cons (f a) (\ α → map f (as α))
map-eq f a b = ap (cons _) (later-ext \ α → pfix' _ α $> b α)

_∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q i = primHComp (\ j → \ { (i = i0) → x; (i = i1) → q j}) (p i)

map-repeat : ∀ {A B : Set} → (a : A) → (f : A → B) → map f (repeat a) ≡ repeat (f a)
map-repeat a f = fix \ prf▹ → ap (map f) (repeat-eq a) ∙ (map-eq f a _ ∙ ap (cons (f a)) (later-ext prf▹ ∙ later-ext \ α → \ i → pfix' (cons (f a)) α (primINeg i) ))


tail : ∀ {A : Set} → gStream A → ▹ gStream A
tail (cons x xs) = xs
