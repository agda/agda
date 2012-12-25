{-# OPTIONS --universe-polymorphism #-}

module 13-implicitProofObligations where

module Imports where
  module L where
    postulate
      Level : Set
      zero  : Level
      suc   : Level → Level
      _⊔_   : Level → Level → Level

    {-# BUILTIN LEVEL     Level #-}
    {-# BUILTIN LEVELZERO zero  #-}
    {-# BUILTIN LEVELSUC  suc   #-}
    {-# BUILTIN LEVELMAX  _⊔_   #-}

  -- extract from Data.Unit
  record ⊤ : Set where
    constructor tt

  -- extract from Data.Empty
  data ⊥ : Set where

  ⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
  ⊥-elim ()

  -- extract from Function
  id : ∀ {a} {A : Set a} → A → A
  id x = x

  _$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
        ((x : A) → B x) → ((x : A) → B x)
  f $ x = f x

  _∘_ : ∀ {a b c}
          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
  f ∘ g = λ x → f (g x)

  -- extract from Data.Bool
  data Bool : Set where
    true  : Bool
    false : Bool

  not : Bool → Bool
  not true  = false
  not false = true

  T : Bool → Set
  T true  = ⊤
  T false = ⊥

  -- extract from Relation.Nullary.Decidable and friends
  infix 3 ¬_

  ¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
  ¬ P = P → ⊥

  data Dec {p} (P : Set p) : Set p where
    yes : ( p :   P) → Dec P
    no  : (¬p : ¬ P) → Dec P
  ⌊_⌋ : ∀ {p} {P : Set p} → Dec P → Bool
  ⌊ yes _ ⌋ = true
  ⌊ no  _ ⌋ = false

  False : ∀ {p} {P : Set p} → Dec P → Set
  False Q = T (not ⌊ Q ⌋)

  -- extract from Relation.Binary.PropositionalEquality
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x

  cong : ∀ {a b} {A : Set a} {B : Set b}
         (f : A → B) {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl

  _≢_ : ∀ {a} {A : Set a} → A → A → Set a
  x ≢ y = ¬ x ≡ y

  -- extract from Data.Nat
  data ℕ : Set where
    zero : ℕ
    suc  : (n : ℕ) → ℕ

  {-# BUILTIN NATURAL ℕ    #-}
  {-# BUILTIN ZERO    zero #-}
  {-# BUILTIN SUC     suc  #-}

  pred : ℕ → ℕ
  pred zero    = zero
  pred (suc n) = n

  infixl 6 _+_ 

  _+_ : ℕ → ℕ → ℕ
  -- zero  + n = n
  -- suc m + n = suc (m + n)
  zero  + n = n
  suc m + n = suc (m + n)

  _*_ : ℕ → ℕ → ℕ
  zero  * n = zero
  suc m * n = n + m * n

  _≟_ : (x y : ℕ) → Dec (x ≡ y)
  zero  ≟ zero   = yes refl
  suc m ≟ suc n  with m ≟ n
  suc m ≟ suc .m | yes refl = yes refl
  suc m ≟ suc n  | no prf   = no (prf ∘ cong pred)
  zero  ≟ suc n  = no λ()
  suc m ≟ zero   = no λ()

  -- extract from Data.Fin
  data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (suc n)
    suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

  -- A conversion: toℕ "n" = n.

  toℕ : ∀ {n} → Fin n → ℕ
  toℕ zero    = 0
  toℕ (suc i) = suc (toℕ i)

  -- extract from Data.Product
  record Σ {a b} (A : Set a) (B : A → Set b) : Set (a L.⊔ b) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  _×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a L.⊔ b)
  A × B = Σ A (λ (_ : A) → B)

  -- extract from Data.Nat.DivMod

  data DivMod : ℕ → ℕ → Set where
    result : {divisor : ℕ} (q : ℕ) (r : Fin divisor) →
             DivMod (toℕ r + q * divisor) divisor

  data DivMod' (dividend divisor : ℕ) : Set where
    result : (q : ℕ) (r : Fin divisor)
             (eq : dividend ≡ (toℕ r + q * divisor)) →
             DivMod' dividend divisor

  postulate
    _div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
    _divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
               DivMod dividend divisor
    _divMod'_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
                        DivMod' dividend divisor

open Imports


-- Begin of actual example!

postulate
  d : ℕ
  d≢0 : d ≢ 0
--  d≢0' : d ≢ 0

fromWitnessFalse : ∀ {p} {P : Set p} {Q : Dec P} → ¬ P → False Q
fromWitnessFalse {Q = yes p} ¬P = ⊥-elim $ ¬P p
fromWitnessFalse {Q = no ¬p} ¬P = tt

⋯ : {A : Set} → {{v : A}} → A
⋯ {{v}} = v

_divMod′_ : (dividend divisor : ℕ) {{ ≢0 : divisor ≢ 0 }} → ℕ × ℕ
_divMod′_ a d {{_}} with _divMod_ a d { fromWitnessFalse ⋯ }
._ divMod′ d | (result q r) = q , toℕ r

_div′_ : (dividend divisor : ℕ) {{ ≢0 : divisor ≢ 0 }} → ℕ
_div′_ a b {{_}} with a divMod′ b
a div′ b | (q , _) = q

--Agda can't resolve hiddens
-- test : {d≢0 : False (d ≟ 0)} → ℕ
-- test = 5 div d
-- test2 : {{d≢0 : d ≢ 0}} → ℕ
-- test2 = 5 div′ d

test3 = 5 div 2
test4 = 5 div′ 2
  where nz : 2 ≢ 0
        nz ()
