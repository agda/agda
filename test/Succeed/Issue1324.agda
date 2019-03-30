------------------------------------------------------------------------
-- Library stuff

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

data Bool : Set where
  true false : Bool

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f


data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_∸_ : ℕ → ℕ → ℕ
m      ∸ zero  = m
zero   ∸ suc n = zero
suc m  ∸ suc n = m ∸ n

_≤_ : ℕ → ℕ → Bool
zero   ≤ n      = true
suc m  ≤ zero   = false
suc m  ≤ suc n  = m ≤ n

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,_]₁ : ∀ {A : Set} {B : Set} {C : A ⊎ B → Set₁} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ]₁ (inj₁ x) = f x
[ f , g ]₁ (inj₂ y) = g y

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

record Σ (X : Set) (Y : X → Set) : Set where
  constructor _,_
  field
    proj₁ : X
    proj₂ : Y proj₁

_×_ : Set → Set → Set
X × Y = Σ X λ _ → Y

record Sig : Set₁ where
  constructor _◃_
  field
    Parameter : Set
    Arity     : Parameter → Set

open Sig public

⟦_⟧ : Sig → Set → Set
⟦ P ◃ A ⟧ X = Σ P λ p → A p → X

Alg : Sig → Set → Set
Alg Σ X = ⟦ Σ ⟧ X → X

data μ (C : Sig) : Set where
  sup : Alg C (μ C)

const^C : Set → Sig
const^C X = X ◃ λ _ → ⊥

_⊎^C_ : Sig → Sig → Sig
(P₁ ◃ A₁) ⊎^C (P₂ ◃ A₂) = (P₁ ⊎ P₂) ◃ [ A₁ , A₂ ]₁

_⋆^C_ : Sig → Set → Sig
C ⋆^C X = const^C X ⊎^C C

_⋆_ : Sig → Set → Set
C ⋆ X = μ (C ⋆^C X)

act : ∀ {C X} → Alg C (C ⋆ X)
act (p , k) = sup (inj₂ p , k)

record Monad (T : Set → Set) : Set₁ where
  infixl 1 _>>=_
  field
    return  : ∀ {X} → X → T X
    _>>=_   : ∀ {X Y} → T X → (X → T Y) → T Y

monad : ∀ {Σ} → Monad (_⋆_ Σ)
monad {Σ} = record
  { return = λ x → sup (inj₁ x , λ ())
  ; _>>=_  = _>>=_
  }
  where
  _>>=_ : ∀ {X Y} → Σ ⋆ X → (X → Σ ⋆ Y) → Σ ⋆ Y
  sup (inj₁ x , _) >>= f = f x
  sup (inj₂ p , k) >>= f = act (p , λ a → k a >>= f)

generic : ∀ {Σ} (p : Parameter Σ) → Σ ⋆ Arity Σ p
generic p = act (p , return)
  where
  open Monad monad

------------------------------------------------------------------------
-- Example

Π : (X : Set) → (X → Set) → Set
Π X Y = (x : X) → (X ◃ Y) ⋆ Y x

call : ∀ {X Y} → Π X Y
call x = generic x

dom : ∀ {X Y} → ∀ {x} → (X ◃ Y) ⋆ Y x → (X → Set) → Set
dom          (sup (inj₁ _ , _))  R = ⊤
dom {Y = Y}  (sup (inj₂ x , k))  R
  = R x × ((y : Y x) → dom (k y) R)

data Dom {X}{Y} (f : (x : X) → (X ◃ Y) ⋆ Y x) : X → Set
  where
  ⟨_⟩ : ∀ {x} → dom (f x) (Dom f) → Dom f x

dom-map : ∀ {X Y} {R₁ R₂ : X → Set} {x}
          {w : (X ◃ Y) ⋆ Y x} →
          (∀ {x} → R₁ x → R₂ x) → dom w R₁ → dom w R₂
dom-map {w = sup (inj₁ _ , _)} f  _         = tt
dom-map {w = sup (inj₂ _ , _)} f  (y₁ , k)  =
  f y₁ , λ y₂ → dom-map f (k y₂)

{-# TERMINATING #-}
bove-capretta : ∀ {X Y} (f : Π X Y) → (x : X) → Dom f x → Y x
bove-capretta {X}{Y} f x ⟨ d ⟩
  = helper (f x) (dom-map (λ {x′} → bove-capretta f x′) d)
  where
  helper : ∀ {x} (w : (X ◃ Y) ⋆ Y x) → dom w Y → Y x
  helper (sup (inj₁ y , _))  _        = y
  helper (sup (inj₂ _ , k)) (d , dk)  = helper (k d) (dk d)

-- AIM XXIX, 2019-03-18, issue #3597
-- Freezing cannot be prevented by eta-expansion any more.
-- WAS:
-- module _ where
--   open Monad monad
--
-- Ulf: proper use of monad would be this:
-- module _ where
--   open module M {Σ} = Monad (monad {Σ})
--
-- Andreas: this works because metas in module parameters are not frozed immediately
module _ (open Monad monad) where

  gcd : Π (ℕ × ℕ) (λ _ →  ℕ)
  gcd (0 , n)          = return n
  gcd (m , 0)          = return m
  gcd (suc m , suc n)  = if m ≤ n
                         then  call (suc m , (n ∸ m))
                         else  call ((m ∸ n) , suc n)

acc : Dom gcd (8 , 12)
acc = ⟨ ⟨ ⟨ ⟨ _ ⟩ , _ ⟩ , _ ⟩ , _ ⟩ -- ⟨ ⟨ ⟨ ⟨ tt ⟩ , (λ _ → tt) ⟩ , (λ _ → tt) ⟩ , (λ _ → tt) ⟩

test-gcd′ : bove-capretta gcd (8 , 12) acc ≡ 4
test-gcd′ = refl
