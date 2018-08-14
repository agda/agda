-- Andreas, 2016-10-03, re issue #2231
-- Testing whether the
{-# OPTIONS --guardedness-preserving-type-constructors #-}
-- stuff works in abstract blocks

-- {-# OPTIONS -v term:30 -v tc.term.expr.coind:100 #-}

module AbstractGuardednessPreservingTypeConstructors where

infix 1000 ♯_

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

-- Preliminaries.

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

data Bool : Set where
  true false : Bool

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Σ cannot be a record type below.

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

data Rec (A : ∞ Set) : Set where
  fold : ♭ A → Rec A

abstract

  -- Corecursive definition of the natural numbers.

  ℕ : Set
  ℕ = ⊤ ⊎ Rec (♯ ℕ)

  zero : ℕ
  zero = inj₁ _

  suc : ℕ → ℕ
  suc n = inj₂ (fold n)

  ℕ-rec : (P : ℕ → Set) →
          P zero →
          (∀ n → P n → P (suc n)) →
          ∀ n → P n
  ℕ-rec P z s (inj₁ _)        = z
  ℕ-rec P z s (inj₂ (fold n)) = s n (ℕ-rec P z s n)

  -- Corecursive definition of the W-type.

  W : (A : Set) → (A → Set) → Set
  W A B = Rec (♯ (Σ[ x ∶ A ] (B x → W A B)))

  syntax W A (λ x → B) = W[ x ∶ A ] B

  sup : {A : Set} {B : A → Set} (x : A) (f : B x → W A B) → W A B
  sup x f = fold (x , f)

  W-rec : {A : Set} {B : A → Set}
          (P : W A B → Set) →
          (∀ {x} {f : B x → W A B} → (∀ y → P (f y)) → P (sup x f)) →
          ∀ x → P x
  W-rec P h (fold (x , f)) = h (λ y → W-rec P h (f y))

-- Induction-recursion encoded as corecursion-recursion.

-- The following definitions are needed on the type level, so we cannot make them abstract.

data Label : Set where
  ′0 ′1 ′2 ′σ ′π ′w : Label

mutual

  U : Set
  U = Σ Label U′

  U′ : Label → Set
  U′ ′0 = ⊤
  U′ ′1 = ⊤
  U′ ′2 = ⊤
  U′ ′σ = Rec (♯ (Σ[ a ∶ U ] (El a → U)))
  U′ ′π = Rec (♯ (Σ[ a ∶ U ] (El a → U)))
  U′ ′w = Rec (♯ (Σ[ a ∶ U ] (El a → U)))

  El : U → Set
  El (′0 , _)            = ⊥
  El (′1 , _)            = ⊤
  El (′2 , _)            = Bool
  El (′σ , fold (a , b)) = Σ[ x ∶ El a ]  El (b x)
  El (′π , fold (a , b)) =   (x : El a) → El (b x)
  El (′w , fold (a , b)) = W[ x ∶ El a ]  El (b x)

-- The recursor can be abstract.

abstract

  U-rec : (P : ∀ u → El u → Set) →
          P (′1 , _) tt →
          P (′2 , _) true →
          P (′2 , _) false →
          (∀ {a b x y} →
           P a x → P (b x) y → P (′σ , fold (a , b)) (x , y)) →
          (∀ {a b f} →
           (∀ x → P (b x) (f x)) → P (′π , fold (a , b)) f) →
          (∀ {a b x f} →
           (∀ y → P (′w , fold (a , b)) (f y)) →
           P (′w , fold (a , b)) (sup x f)) →
          ∀ u (x : El u) → P u x
  U-rec P P1 P2t P2f Pσ Pπ Pw = rec
    where
    rec : ∀ u (x : El u) → P u x
    rec (′0 , _)            ()
    rec (′1 , _)            _              = P1
    rec (′2 , _)            true           = P2t
    rec (′2 , _)            false          = P2f
    rec (′σ , fold (a , b)) (x , y)        = Pσ (rec _ x) (rec _ y)
    rec (′π , fold (a , b)) f              = Pπ (λ x → rec _ (f x))
    rec (′w , fold (a , b)) (fold (x , f)) = Pw (λ y → rec _ (f y))
