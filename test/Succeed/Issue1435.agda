-- Reported by nils.anders.danielsson, Feb 17, 2015

-- See also  Issue 292 ,  Issue 1406 , and Issue 1427.

-- The code below is accepted by Agda 2.4.2.2, but not by the current
-- maintenance or master branches.

data Box (A : Set) : Set where
  [_] : A → Box A

data _≡_ (A : Set) : Set → Set₁ where
  refl : A ≡ A

data _≅_ {A : Set₁} (x : A) : {B : Set₁} → B → Set₂ where
  refl : x ≅ x

-- C could be a typed DSEL.

data C : Set → Set₁ where
  c₁ c₂ : (A : Set) → C (Box A)
-- If A is considered forced, the code no longer type-checks.

-- D could be some kind of semantics for C.

data D : {A : Set} → C A → Set₂ where
  d₁ : (A : Set) → D (c₁ A)
  d₂ : (A : Set) → D (c₂ A)

module Doesn't-work where

  -- Let's try to write an eliminator for the part of the semantics
  -- that concerns c₁ programs. The basic approach doesn't work:

  D-elim-c₁ : (P : {A : Set} → D (c₁ A) → Set₂) →
              ((A : Set) → P (d₁ A)) →
              {A : Set} (x : D (c₁ A)) → P x
  D-elim-c₁ P p (d₁ A) = p A

  -- The following trick also fails (but for some reason the absurd
  -- case is accepted):

  -- Jesper 2015-12-18 update: this is no longer accepted by the new unifier.
  --D-elim-c₁-helper :
  --  (P : {A B : Set} {c : C A} →
  --       D c → A ≡ Box B → c ≅ c₁ B → Set₂) →
  --  ((A : Set) → P (d₁ A) refl refl) →
  --  {A B : Set} {c : C A}
  --  (x : D c) (eq₂ : c ≅ c₁ B) (eq₁ : A ≡ Box B) → P x eq₁ eq₂
  --D-elim-c₁-helper P p (d₂ A) ()   _
  --D-elim-c₁-helper P p (d₁ A) refl refl = p A

module Works where

  -- I can define the eliminators by first defining and proving no
  -- confusion (following McBride, Goguen and McKinna). However, this
  -- requires a fair amount of work, and easy dependent pattern
  -- matching is arguably one of the defining features of Agda.
  --
  -- A quote from "A Few Constructions on Constructors": "The Epigram
  -- language and system [25, 23] takes these constructions for
  -- granted. We see no reason why the users of other systems should
  -- work harder than we do."

  data ⊥ : Set₁ where

  No-confusion : ∀ {A B} → C A → C B → Set₁
  No-confusion (c₁ A) (c₁ B) = A ≡ B
  No-confusion (c₂ A) (c₂ B) = A ≡ B
  No-confusion _      _      = ⊥

  no-confusion :
    ∀ {A B} (x : C A) (y : C B) → A ≡ B → x ≅ y → No-confusion x y
  no-confusion (c₁ A) .(c₁ A) refl refl = refl
  no-confusion (c₂ A) .(c₂ A) refl refl = refl

  D-elim-c₁-helper :
    (P : {A B : Set} {c : C A} →
         D c → A ≡ Box B → c ≅ c₁ B → Set₂) →
    ((A : Set) → P (d₁ A) refl refl) →
    {A B : Set} {c : C A}
    (x : D c) (eq₂ : c ≅ c₁ B) (eq₁ : A ≡ Box B) → P x eq₁ eq₂
  D-elim-c₁-helper P p (d₁ A) eq₂  eq₁  with no-confusion _ _ eq₁ eq₂
  D-elim-c₁-helper P p (d₁ B) refl refl | refl = p B
  D-elim-c₁-helper P p (d₂ A) eq₂  eq₁  with no-confusion _ _ eq₁ eq₂
  D-elim-c₁-helper P p (d₂ A) eq₂  eq₁  | ()

  cast : {A B : Set} {x : C A} {y : C B} →
         A ≡ B → x ≅ y → D x → D y
  cast refl refl x = x

  D-elim-c₁ :
    (P : {A : Set} → D (c₁ A) → Set₂) →
    ((A : Set) → P (d₁ A)) →
    {A : Set} (x : D (c₁ A)) → P x
  D-elim-c₁ P p x =
    D-elim-c₁-helper (λ x eq₁ eq₂ → P (cast eq₁ eq₂ x)) p x refl refl

-- should type-check
