------------------------------------------------------------------------
-- The partiality monad
------------------------------------------------------------------------

module Category.Monad.Partiality where

open import Coinduction
open import Category.Monad
open import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod
open import Data.Sum
open import Function
open import Function.Equivalence using (_⇔_; equivalent)
open import Relation.Binary hiding (Rel)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

------------------------------------------------------------------------
-- The partiality monad

data _⊥ (A : Set) : Set where
  now   : (x : A) → A ⊥
  later : (x : ∞ (A ⊥)) → A ⊥

monad : RawMonad _⊥
monad = record
  { return = now
  ; _>>=_  = _>>=_
  }
  where
  _>>=_ : ∀ {A B} → A ⊥ → (A → B ⊥) → B ⊥
  now x   >>= f = f x
  later x >>= f = later (♯ (♭ x >>= f))

private module M = RawMonad monad

-- Non-termination.

never : {A : Set} → A ⊥
never = later (♯ never)

-- run x for n steps peels off at most n "later" constructors from x.

run_for_steps : ∀ {A} → A ⊥ → ℕ → A ⊥
run now   x for n     steps = now x
run later x for zero  steps = later x
run later x for suc n steps = run ♭ x for n steps

-- Is the computation done?

isNow : ∀ {A} → A ⊥ → Bool
isNow (now x)   = true
isNow (later x) = false

------------------------------------------------------------------------
-- Kinds

-- The partiality monad comes with two forms of equality (weak and
-- strong) and one ordering. Strong equality is stronger than the
-- ordering, which is stronger than weak equality.

-- The three relations are defined using a single data type, indexed
-- by a "kind".

data OtherKind : Set where
  geq weak : OtherKind

data Kind : Set where
  strong : Kind
  other  : (k : OtherKind) → Kind

-- Kind equality is decidable.

_≟-Kind_ : Decidable (_≡_ {A = Kind})
_≟-Kind_ strong       strong       = yes P.refl
_≟-Kind_ strong       (other k)    = no λ()
_≟-Kind_ (other k)    strong       = no λ()
_≟-Kind_ (other geq)  (other geq)  = yes P.refl
_≟-Kind_ (other geq)  (other weak) = no λ()
_≟-Kind_ (other weak) (other geq)  = no λ()
_≟-Kind_ (other weak) (other weak) = yes P.refl

-- A predicate which is satisfied only for equalities. Note that, for
-- concrete inputs, this predicate evaluates to ⊤ or ⊥.

Equality : Kind → Set
Equality k = False (k ≟-Kind other geq)

------------------------------------------------------------------------
-- Equality/ordering

-- The three relations.

data Rel {A : Set} : Kind → A ⊥ → A ⊥ → Set where
  now    : ∀ {k v}                                         → Rel k         (now   v) (now   v)
  later  : ∀ {k x y} (x∼y : ∞ (Rel k         (♭ x) (♭ y))) → Rel k         (later x) (later y)
  laterʳ : ∀ {x y}   (x≈y :    Rel (other weak) x  (♭ y) ) → Rel (other weak)     x  (later y)
  laterˡ : ∀ {k x y} (x∼y :    Rel (other k) (♭ x)    y  ) → Rel (other k) (later x)        y

infix 4 _≅_ _≳_ _≲_ _≈_

_≅_ : {A : Set} → A ⊥ → A ⊥ → Set
_≅_ = Rel strong

_≳_ : {A : Set} → A ⊥ → A ⊥ → Set
_≳_ = Rel (other geq)

_≲_ : {A : Set} → A ⊥ → A ⊥ → Set
_≲_ = flip _≳_

_≈_ : {A : Set} → A ⊥ → A ⊥ → Set
_≈_ = Rel (other weak)

------------------------------------------------------------------------
-- Lemmas relating the three relations

-- All relations include strong equality.

≅⇒ : ∀ {A : Set} {k} {x y : A ⊥} → x ≅ y → Rel k x y
≅⇒ now         = now
≅⇒ (later x≅y) = later (♯ ≅⇒ (♭ x≅y))

-- The weak equality includes the ordering.

≳⇒ : ∀ {A : Set} {k} {x y : A ⊥} → x ≳ y → Rel (other k) x y
≳⇒ now          = now
≳⇒ (later  x≳y) = later (♯ ≳⇒ (♭ x≳y))
≳⇒ (laterˡ x≳y) = laterˡ  (≳⇒    x≳y )

-- The relations agree for non-terminating computations.

never⇒never : ∀ {A : Set} {k₁ k₂} {x : A ⊥} →
              Rel k₁ x never → Rel k₂ x never
never⇒never (later  x∼never) = later (♯ never⇒never (♭ x∼never))
never⇒never (laterʳ x≈never) =          never⇒never    x≈never
never⇒never (laterˡ x∼never) = later (♯ never⇒never    x∼never)

-- The "other" relations agree when the right-hand side is a value.

now⇒now : ∀ {A : Set} {k₁ k₂} {x} {y : A} →
          Rel (other k₁) x (now y) → Rel (other k₂) x (now y)
now⇒now now            = now
now⇒now (laterˡ x∼now) = laterˡ (now⇒now x∼now)

------------------------------------------------------------------------
-- The relations are equivalences or partial orders

-- Later can be dropped.

laterʳ⁻¹ : ∀ {A : Set} {k} {x : A ⊥} {y} →
           Rel (other k) x (later y) → Rel (other k) x (♭ y)
laterʳ⁻¹ (later  x∼y)  = laterˡ        (♭ x∼y)
laterʳ⁻¹ (laterʳ x≈y)  = x≈y
laterʳ⁻¹ (laterˡ x∼ly) = laterˡ (laterʳ⁻¹ x∼ly)

laterˡ⁻¹ : ∀ {A : Set} {x} {y : A ⊥} → later x ≈ y → ♭ x ≈ y
laterˡ⁻¹ (later  x≈y)  = laterʳ         (♭ x≈y)
laterˡ⁻¹ (laterʳ lx≈y) = laterʳ (laterˡ⁻¹ lx≈y)
laterˡ⁻¹ (laterˡ x≈y)  = x≈y

later⁻¹ : ∀ {A : Set} {k} {x y : ∞ (A ⊥)} →
          Rel k (later x) (later y) → Rel k (♭ x) (♭ y)
later⁻¹ (later  x∼y)  = ♭ x∼y
later⁻¹ (laterʳ lx≈y) = laterˡ⁻¹ lx≈y
later⁻¹ (laterˡ x∼ly) = laterʳ⁻¹ x∼ly

-- All the relations are preorders.

preorder : Kind → Set → Preorder _ _ _
preorder k A = record
  { Carrier    = A ⊥
  ; _≈_        = _≡_
  ; _∼_        = Rel k
  ; isPreorder = record
    { isEquivalence = P.isEquivalence
    ; reflexive     = refl _
    ; trans         = trans
    }
  }
  where
  refl : ∀ {k} (x : A ⊥) {y} → x ≡ y → Rel k x y
  refl (now v)   P.refl = now
  refl (later x) P.refl = later (♯ refl (♭ x) P.refl)

  now-trans : ∀ {k x y} {v : A} →
              Rel k x y → Rel k y (now v) → Rel k x (now v)
  now-trans x∼y  now          = x∼y
  now-trans x∼ly (laterˡ y∼z) = now-trans (laterʳ⁻¹ x∼ly) y∼z

  mutual

    later-trans : ∀ {k} {x y : A ⊥} {z} →
                  Rel k x y → Rel k y (later z) → Rel k x (later z)
    later-trans (later  x∼y) (later  y∼z)  = later  (♯ trans (♭ x∼y)         (♭ y∼z))
    later-trans (later  x∼y) (laterˡ y∼lz) = later  (♯ trans (♭ x∼y) (laterʳ⁻¹  y∼lz))
    later-trans (laterˡ x∼y)         y∼lz  = later  (♯ trans    x∼y  (laterʳ⁻¹  y∼lz))
    later-trans (laterʳ x≈y)        ly≈lz  =     later-trans    x≈y  (laterˡ⁻¹ ly≈lz)
    later-trans         x≈y  (laterʳ y≈z)  = laterʳ (  trans    x≈y             y≈z )

    trans : ∀ {k} {x y z : A ⊥} → Rel k x y → Rel k y z → Rel k x z
    trans {z = now v}   x∼y y∼v  = now-trans   x∼y y∼v
    trans {z = later z} x∼y y∼lz = later-trans x∼y y∼lz

private module Pre {k} {A : Set} = Preorder (preorder k A)

-- The two equalities are equivalence relations.

setoid : (k : Kind) {eq : Equality k} → Set → Setoid _ _
setoid k {eq} A = record
  { Carrier       = A ⊥
  ; _≈_           = Rel k
  ; isEquivalence = record
    { refl  = Pre.refl
    ; sym   = sym eq
    ; trans = Pre.trans
    }
  }
  where
  sym : ∀ {k} {x y : A ⊥} → Equality k → Rel k x y → Rel k y x
  sym eq now                 = now
  sym eq (later         x∼y) = later (♯ sym eq (♭ x∼y))
  sym eq (laterʳ        x≈y) = laterˡ  (sym eq    x≈y )
  sym eq (laterˡ {weak} x≈y) = laterʳ  (sym eq    x≈y )
  sym () (laterˡ {geq}  x≳y)

private module S {k} {eq} {A : Set} = Setoid (setoid k {eq} A)

-- The order is a partial order, with strong equality as the
-- underlying equality.

≳-poset : Set → Poset _ _ _
≳-poset A = record
  { Carrier        = A ⊥
  ; _≈_            = _≅_
  ; _≤_            = _≳_
  ; isPartialOrder = record
    { antisym    = antisym
    ; isPreorder = record
      { isEquivalence = S.isEquivalence
      ; reflexive     = ≅⇒
      ; trans         = Pre.trans
      }
    }
  }
  where
  antisym : {x y : A ⊥} → x ≳ y → x ≲ y → x ≅ y
  antisym now           now           = now
  antisym (later  x≳y)  (later  x≲y)  = later (♯ antisym        (♭ x≳y)         (♭ x≲y))
  antisym (later  x≳y)  (laterˡ x≲ly) = later (♯ antisym        (♭ x≳y)  (laterʳ⁻¹ x≲ly))
  antisym (laterˡ x≳ly) (later  x≲y)  = later (♯ antisym (laterʳ⁻¹ x≳ly)        (♭ x≲y))
  antisym (laterˡ x≳ly) (laterˡ x≲ly) = later (♯ antisym (laterʳ⁻¹ x≳ly) (laterʳ⁻¹ x≲ly))

-- Equational reasoning.

module RelReasoning where

  infix  2 _∎
  infixr 2 _≅⟨_⟩_ _≳⟨_⟩_ _≈⟨_⟩_

  _≅⟨_⟩_ : ∀ {k A} x {y z : A ⊥} → x ≅ y → Rel k y z → Rel k x z
  _ ≅⟨ x≅y ⟩ y∼z = Pre.trans (≅⇒ x≅y) y∼z

  _≳⟨_⟩_ : ∀ {k A} x {y z : A ⊥} →
           x ≳ y → Rel (other k) y z → Rel (other k) x z
  _ ≳⟨ x≳y ⟩ y∼z = Pre.trans (≳⇒ x≳y) y∼z

  _≈⟨_⟩_ : ∀ {A} x {y z : A ⊥} → x ≈ y → y ≈ z → x ≈ z
  _ ≈⟨ x≈y ⟩ y≈z = Pre.trans x≈y y≈z

  open S public using (sym)

  _∎ : ∀ {k A} (x : A ⊥) → Rel k x x
  x ∎ = Pre.refl

------------------------------------------------------------------------
-- Terminating computations

-- x ⇓ y means that x terminates with y.

infix 4 _⇓[_]_ _⇓_

_⇓[_]_ : {A : Set} → A ⊥ → Kind → A → Set
x ⇓[ k ] y = Rel k x (now y)

_⇓_ : {A : Set} → A ⊥ → A → Set
x ⇓ y = x ⇓[ other weak ] y

-- The number of later constructors (steps) in the terminating
-- computation x.

steps : ∀ {k} {A : Set} {x : A ⊥} {y} → x ⇓[ k ] y → ℕ
steps .{x = now   v} (now    {v = v})    = zero
steps .{x = later x} (laterˡ {x = x} x⇓) = suc (steps {x = ♭ x} x⇓)

module Steps where

  open P.≡-Reasoning
  open RelReasoning using (_≅⟨_⟩_)

  private

    lemma : ∀ {k} {A : Set} {x y} {z : A}
            (x∼y : Rel (other k) (♭ x) y)
            (y⇓z : y ⇓[ other k ] z) →
            steps (Pre.trans (laterˡ {x = x} x∼y) y⇓z) ≡
            suc (steps (Pre.trans x∼y y⇓z))
    lemma x∼y now          = P.refl
    lemma x∼y (laterˡ y⇓z) = begin
      steps (Pre.trans (laterˡ (laterʳ⁻¹ x∼y)) y⇓z)  ≡⟨ lemma (laterʳ⁻¹ x∼y) y⇓z ⟩
      suc (steps (Pre.trans (laterʳ⁻¹ x∼y) y⇓z))     ∎

  left-identity : ∀ {k} {A : Set} {x y} {z : A}
                  (x≅y : x ≅ y) (y⇓z : y ⇓[ k ] z) →
                  steps (x ≅⟨ x≅y ⟩ y⇓z) ≡ steps y⇓z
  left-identity now         now          = P.refl
  left-identity (later x≅y) (laterˡ y⇓z) = begin
    steps (Pre.trans (laterˡ (≅⇒ (♭ x≅y))) y⇓z)  ≡⟨ lemma (≅⇒ (♭ x≅y)) y⇓z ⟩
    suc (steps (_ ≅⟨ ♭ x≅y ⟩ y⇓z))               ≡⟨ P.cong suc $ left-identity (♭ x≅y) y⇓z ⟩
    suc (steps y⇓z)                              ∎

  right-identity : ∀ {k} {A : Set} {x} {y z : A}
                   (x⇓y : x ⇓[ k ] y) (y≈z : now y ⇓[ k ] z) →
                   steps (Pre.trans x⇓y y≈z) ≡ steps x⇓y
  right-identity x⇓y now = P.refl

------------------------------------------------------------------------
-- Non-terminating computations

-- x ⇑ means that x does not terminate.

infix 4 _⇑[_] _⇑

_⇑[_] : {A : Set} → A ⊥ → Kind → Set
x ⇑[ k ] = Rel k x never

_⇑ : {A : Set} → A ⊥ → Set
x ⇑ = x ⇑[ other weak ]

------------------------------------------------------------------------
-- Lemmas related to now and never

-- Now is not never.

now≉never : ∀ {k} {A : Set} {x : A} → ¬ Rel k (now x) never
now≉never (laterʳ hyp) = now≉never hyp

-- A partial value is either now or never (classically).

now-or-never : ∀ {k} {A : Set} (x : A ⊥) →
               ¬ ¬ ((∃ λ y → x ⇓[ other k ] y) ⊎ x ⇑[ other k ])
now-or-never {A = A} x = helper <$> excluded-middle
  where
  open RawMonad ¬¬-Monad

  not-now-is-never : (x : A ⊥) → (∄ λ y → x ≳ now y) → x ≳ never
  not-now-is-never (now x)   hyp with hyp (, now)
  ... | ()
  not-now-is-never (later x) hyp =
    later (♯ not-now-is-never (♭ x) (hyp ∘ Prod.map id laterˡ))

  helper : Dec (∃ λ y → x ≳ now y) → _
  helper (yes ≳now) = inj₁ $ Prod.map id ≳⇒ ≳now
  helper (no  ≵now) = inj₂ $ ≳⇒ $ not-now-is-never x ≵now

------------------------------------------------------------------------
-- Laws related to bind

-- Bind preserves all the relations.

_>>=-cong_ :
  ∀ {A B : Set} {k} {x₁ x₂ : A ⊥} {f₁ f₂ : A → B ⊥} → let open M in
  Rel k x₁ x₂ → (∀ x → Rel k (f₁ x) (f₂ x)) →
  Rel k (x₁ >>= f₁) (x₂ >>= f₂)
now          >>=-cong f₁∼f₂ = f₁∼f₂ _
later  x₁∼x₂ >>=-cong f₁∼f₂ = later (♯ (♭ x₁∼x₂ >>=-cong f₁∼f₂))
laterʳ x₁≈x₂ >>=-cong f₁≈f₂ = laterʳ (x₁≈x₂ >>=-cong f₁≈f₂)
laterˡ x₁∼x₂ >>=-cong f₁∼f₂ = laterˡ (x₁∼x₂ >>=-cong f₁∼f₂)

-- Inversion lemmas for bind.

>>=-inversion-⇓ :
  ∀ {k} {A B : Set} x {f : A → B ⊥} {y} → let open M in
  (x>>=f⇓ : (x >>= f) ⇓[ k ] y) →
  ∃ λ z → ∃₂ λ (x⇓ : x ⇓[ k ] z) (fz⇓ : f z ⇓[ k ] y) →
               steps x⇓ + steps fz⇓ ≡ steps x>>=f⇓
>>=-inversion-⇓ (now x)   fx⇓             = (x , now , fx⇓ , P.refl)
>>=-inversion-⇓ (later x) (laterˡ x>>=f⇓) =
  Prod.map id (Prod.map laterˡ (Prod.map id (P.cong suc))) $
    >>=-inversion-⇓ (♭ x) x>>=f⇓

>>=-inversion-⇑ : ∀ {k} {A B : Set} x {f : A → B ⊥} → let open M in
                  Rel (other k) (x >>= f) never →
                  ¬ ¬ (x ⇑[ other k ] ⊎
                       ∃ λ y → x ⇓[ other k ] y × f y ⇑[ other k ])
>>=-inversion-⇑ {A = A} x {f} ∼never = helper <$> now-or-never x
  where
  open RawMonad ¬¬-Monad using (_<$>_)
  open M using (_>>=_)

  is-never : ∀ {x y} → x ≳ now y → (x >>= f) ≳ never → f y ≳ never
  is-never now           = id
  is-never (laterˡ ≳now) = is-never ≳now ∘ later⁻¹

  helper : (∃ λ y → x ≳ now y) ⊎ x ≳ never → _
  helper (inj₂ ≳never)     = inj₁ $ ≳⇒ ≳never
  helper (inj₁ (y , ≳now)) =
    inj₂ (y , ≳⇒ ≳now , ≳⇒ (is-never ≳now (never⇒never ∼never)))

-- Never is a left and right "zero" of bind.

left-zero : {A B : Set} (f : A → B ⊥) → let open M in
            (never >>= f) ≅ never
left-zero f = later (♯ left-zero f)

right-zero : {A B : Set} (x : A ⊥) → let open M in
             (x >>= λ _ → never) ≅ never {A = B}
right-zero (now   x) = S.refl
right-zero (later x) = later (♯ right-zero (♭ x))

-- Now is a left and right identity of bind.

left-identity : {A B : Set} (x : A) (f : A → B ⊥) → let open M in
                (now x >>= f) ≅ f x
left-identity x f = S.refl

right-identity : {A : Set} (x : A ⊥) → let open M in
                 (x >>= now) ≅ x
right-identity (now   x) = now
right-identity (later x) = later (♯ right-identity (♭ x))

-- Bind is associative.

associative : {A B C : Set} (x : A ⊥) (f : A → B ⊥) (g : B → C ⊥) →
              let open M in
              (x >>= f >>= g) ≅ (x >>= λ y → f y >>= g)
associative (now x)   f g = S.refl
associative (later x) f g = later (♯ associative (♭ x) f g)

------------------------------------------------------------------------
-- Productivity checker workaround

-- The monad can be awkward to use, due to the limitations of guarded
-- coinduction. The following code provides a (limited) workaround.

module Workaround where

  infixl 1 _>>=_

  data _⊥P : Set → Set₁ where
    now   : ∀ {A} (x : A) → A ⊥P
    later : ∀ {A} (x : ∞ (A ⊥P)) → A ⊥P
    _>>=_ : ∀ {A B} (x : A ⊥P) (f : A → B ⊥P) → B ⊥P

  private

    data _⊥W : Set → Set₁ where
      now   : ∀ {A} (x : A) → A ⊥W
      later : ∀ {A} (x : A ⊥P) → A ⊥W

    mutual

      _>>=W_ : ∀ {A B} → A ⊥W → (A → B ⊥P) → B ⊥W
      now   x >>=W f = whnf (f x)
      later x >>=W f = later (x >>= f)

      whnf : ∀ {A} → A ⊥P → A ⊥W
      whnf (now   x) = now x
      whnf (later x) = later (♭ x)
      whnf (x >>= f) = whnf x >>=W f

  mutual

    private

      ⟦_⟧W : ∀ {A} → A ⊥W → A ⊥
      ⟦ now   x ⟧W = now x
      ⟦ later x ⟧W = later (♯ ⟦ x ⟧P)

    ⟦_⟧P : ∀ {A} → A ⊥P → A ⊥
    ⟦ x ⟧P = ⟦ whnf x ⟧W

  -- The definitions above make sense. ⟦_⟧P is homomorphic with
  -- respect to now, later and _>>=_.

  now-hom : ∀ {A} (x : A) → ⟦ now x ⟧P ≅ now x
  now-hom _ = S.refl

  later-hom : ∀ {A} (x : ∞ (A ⊥P)) →
              ⟦ later x ⟧P ≅ later (♯ ⟦ ♭ x ⟧P)
  later-hom x = later (♯ S.refl)

  mutual

    private

      >>=-homW : ∀ {A B} (x : A ⊥W) (f : A → B ⊥P) →
                 ⟦ x >>=W f ⟧W ≅ M._>>=_ ⟦ x ⟧W (λ y → ⟦ f y ⟧P)
      >>=-homW (now   x) f = S.refl
      >>=-homW (later x) f = later (♯ >>=-hom x f)

    >>=-hom : ∀ {A B} (x : A ⊥P) (f : A → B ⊥P) →
              ⟦ x >>= f ⟧P ≅ M._>>=_ ⟦ x ⟧P (λ y → ⟦ f y ⟧P)
    >>=-hom x f = >>=-homW (whnf x) f

------------------------------------------------------------------------
-- An alternative, but equivalent, formulation of equality/ordering

module AlternativeRel where

  infix  4 _≅P_ _≳P_ _≈P_
  infix  2 _∎
  infixr 2 _≅⟨_⟩_ _≳⟨_⟩_ _≳⟨_⟩≅_ _≳⟨_⟩≈_ _≈⟨_⟩≅_ _≈⟨_⟩≲_
  infixl 1 _>>=_

  mutual

    -- Proof "programs".

    _≅P_ : {A : Set} → A ⊥ → A ⊥ → Set₁
    _≅P_ = RelP strong

    _≳P_ : {A : Set} → A ⊥ → A ⊥ → Set₁
    _≳P_ = RelP (other geq)

    _≈P_ : {A : Set} → A ⊥ → A ⊥ → Set₁
    _≈P_ = RelP (other weak)

    data RelP {A : Set} : Kind → A ⊥ → A ⊥ → Set₁ where

      -- Congruences.

      now   : ∀ {k v} → RelP k (now v) (now v)
      later : ∀ {k x y} (x∼y : ∞ (RelP k (♭ x) (♭ y))) →
              RelP k (later x) (later y)
      _>>=_ : ∀ {B : Set} {k} {x₁ x₂} {f₁ f₂ : B → A ⊥} → let open M in
              (x₁∼x₂ : RelP k x₁ x₂)
              (f₁∼f₂ : ∀ x → RelP k (f₁ x) (f₂ x)) →
              RelP k (x₁ >>= f₁) (x₂ >>= f₂)

      -- Ordering/weak equality.

      laterʳ : ∀   {x y} (x≈y : RelP (other weak) x (♭ y)) → RelP (other weak)     x (later y)
      laterˡ : ∀ {k x y} (x∼y : RelP (other k) (♭ x)   y)  → RelP (other k) (later x)       y

      -- Equational reasoning. Note that including full transitivity
      -- for weak equality would make _≈P_ trivial; a similar problem
      -- applies to _≳P_ (never ≳P now x would be provable). Instead
      -- the definition of RelP includes limited notions of
      -- transitivity, similar to weak bisimulation up-to various
      -- things.

      _∎      : ∀ {k} x → RelP k x x
      sym     : ∀ {k x y} {eq : Equality k} (x∼y : RelP k x y) → RelP k y x
      _≅⟨_⟩_  : ∀ {k} x {y z} (x≅y : x ≅P y) (y∼z : RelP k y z) → RelP k x z
      _≳⟨_⟩_  : ∀     x {y z} (x≳y : x ≳  y) (y≳z : y ≳P z) → x ≳P z
      _≳⟨_⟩≅_ : ∀     x {y z} (x≳y : x ≳P y) (y≅z : y ≅P z) → x ≳P z
      _≳⟨_⟩≈_ : ∀     x {y z} (x≳y : x ≳P y) (y≈z : y ≈P z) → x ≈P z
      _≈⟨_⟩≅_ : ∀     x {y z} (x≈y : x ≈P y) (y≅z : y ≅P z) → x ≈P z
      _≈⟨_⟩≲_ : ∀     x {y z} (x≈y : x ≈P y) (y≲z : z ≳P y) → x ≈P z

      -- If any of the following transitivity-like rules were added to
      -- RelP, then RelP and Rel would no longer be equivalent:
      --
      --   x ≳P y → y ≳P z → x ≳P z
      --   x ≳P y → y ≳  z → x ≳P z
      --   x ≲P y → y ≈P z → x ≈P z
      --   x ≈P y → y ≳P z → x ≈P z
      --   x ≲  y → y ≈P z → x ≈P z
      --   x ≈P y → y ≳  z → x ≈P z
      --   x ≈P y → y ≈P z → x ≈P z
      --   x ≈P y → y ≈  z → x ≈P z
      --   x ≈  y → y ≈P z → x ≈P z
      --
      -- The reason is that any of these rules would make it possible
      -- to derive that never and now x are related.

  -- RelP is complete with respect to Rel.

  complete : ∀ {A : Set} {k} {x y : A ⊥} → Rel k x y → RelP k x y
  complete now          = now
  complete (later  x∼y) = later (♯ complete (♭ x∼y))
  complete (laterʳ x≈y) = laterʳ  (complete    x≈y)
  complete (laterˡ x∼y) = laterˡ  (complete    x∼y)

  -- RelP is sound with respect to Rel.

  private

    -- Proof WHNFs.

    data RelW {A : Set} : Kind → A ⊥ → A ⊥ → Set₁ where
      now    : ∀ {k v}                                      → RelW k         (now   v) (now   v)
      later  : ∀ {k x y} (x∼y : RelP k         (♭ x) (♭ y)) → RelW k         (later x) (later y)
      laterʳ : ∀   {x y} (x≈y : RelW (other weak) x  (♭ y)) → RelW (other weak)     x  (later y)
      laterˡ : ∀ {k x y} (x∼y : RelW (other k) (♭ x)    y)  → RelW (other k) (later x)        y

    -- WHNFs can be turned into programs.

    program : ∀ {A : Set} {k} {x y : A ⊥} → RelW k x y → RelP k x y
    program now          = now
    program (later  x∼y) = later (♯ x∼y)
    program (laterˡ x∼y) = laterˡ (program x∼y)
    program (laterʳ x≈y) = laterʳ (program x≈y)

    -- Lemmas for WHNFs.

    _>>=W_ :
      ∀ {A B : Set} {k} {x₁ x₂} {f₁ f₂ : B → A ⊥} →
      RelW k x₁ x₂ → (∀ x → RelW k (f₁ x) (f₂ x)) →
      RelW k (M._>>=_ x₁ f₁) (M._>>=_ x₂ f₂)
    now        >>=W f₁∼f₂ = f₁∼f₂ _
    later  x∼y >>=W f₁∼f₂ = later  (x∼y >>= program ∘ f₁∼f₂)
    laterʳ x≈y >>=W f₁≈f₂ = laterʳ (x≈y >>=W f₁≈f₂)
    laterˡ x∼y >>=W f₁∼f₂ = laterˡ (x∼y >>=W f₁∼f₂)

    reflW : ∀ {A : Set} {k} (x : A ⊥) → RelW k x x
    reflW (now   x) = now
    reflW (later x) = later (♭ x ∎)

    symW : ∀ {A : Set} {k} {x y : A ⊥} →
           Equality k → RelW k x y → RelW k y x
    symW eq now                 = now
    symW eq (later         x≈y) = later  (sym {eq = eq} x≈y)
    symW eq (laterʳ        x≈y) = laterˡ (symW      eq  x≈y)
    symW eq (laterˡ {weak} x≈y) = laterʳ (symW      eq  x≈y)
    symW () (laterˡ {geq}  x≈y)

    trans≅W : {A : Set} {x y z : A ⊥} →
              RelW strong x y → RelW strong y z → RelW strong x z
    trans≅W        x≅y  now         = x≅y
    trans≅W (later x≅y) (later y≅z) = later (_ ≅⟨ x≅y ⟩ y≅z)

    trans≳-W : {A : Set} {x y z : A ⊥} →
               x ≳ y → RelW (other geq) y z → RelW (other geq) x z
    trans≳-W now          now          = now
    trans≳-W (later  x≳y) (later  y≳z) = later (_ ≳⟨ ♭ x≳y ⟩ y≳z)
    trans≳-W (later  x≳y) (laterˡ y≳z) = laterˡ (trans≳-W (♭ x≳y) y≳z)
    trans≳-W (laterˡ x≳y)         y≳z  = laterˡ (trans≳-W    x≳y  y≳z)

    -- Strong equality programs can be turned into WHNFs.

    whnf≅ : ∀ {A} {x y : A ⊥} → x ≅P y → RelW strong x y
    whnf≅ now               = now
    whnf≅ (later x≅y)       = later (♭ x≅y)
    whnf≅ (x₁≅x₂ >>= f₁≅f₂) = whnf≅ x₁≅x₂ >>=W λ x → whnf≅ (f₁≅f₂ x)
    whnf≅ (x ∎)             = reflW x
    whnf≅ (sym x≅y)         = symW _ (whnf≅ x≅y)
    whnf≅ (x ≅⟨ x≅y ⟩ y≅z)  = trans≅W (whnf≅     x≅y) (whnf≅ y≅z)

    -- More transitivity lemmas.

    _⟨_⟩≅_ : ∀ {A : Set} {k} x {y z : A ⊥} →
             RelP k x y → y ≅P z → RelP k x z
    _⟨_⟩≅_ {k = strong}     x x≅y y≅z = x ≅⟨ x≅y ⟩  y≅z
    _⟨_⟩≅_ {k = other geq}  x x≳y y≅z = x ≳⟨ x≳y ⟩≅ y≅z
    _⟨_⟩≅_ {k = other weak} x x≈y y≅z = x ≈⟨ x≈y ⟩≅ y≅z

    trans∼≅W : ∀ {A : Set} {k} {x y z : A ⊥} →
               RelW k x y → RelW strong y z → RelW k x z
    trans∼≅W         x∼y  now         = x∼y
    trans∼≅W (later  x∼y) (later y≅z) = later (_ ⟨ x∼y ⟩≅ y≅z)
    trans∼≅W (laterʳ x≈y) (later y≅z) = laterʳ (trans∼≅W x≈y (whnf≅ y≅z))
    trans∼≅W (laterˡ x∼y)        y≅z  = laterˡ (trans∼≅W x∼y        y≅z)

    trans≅∼W : ∀ {A : Set} {k} {x y z : A ⊥} →
               RelW strong x y → RelW k y z → RelW k x z
    trans≅∼W now                  y∼z  = y∼z
    trans≅∼W (later x≅y) (later   y∼z) = later (_ ≅⟨ x≅y ⟩ y∼z)
    trans≅∼W (later x≅y) (laterˡ  y∼z) = laterˡ (trans≅∼W (whnf≅ x≅y) y∼z)
    trans≅∼W        x≅y  (laterʳ ly≈z) = laterʳ (trans≅∼W        x≅y ly≈z)

    -- Order programs can be turned into WHNFs.

    whnf≳ : ∀ {A : Set} {x y : A ⊥} → x ≳P y → RelW (other geq) x y
    whnf≳ now                 = now
    whnf≳ (later  x∼y)        = later (♭ x∼y)
    whnf≳ (laterˡ x≲y)        = laterˡ (whnf≳ x≲y)
    whnf≳ (x₁∼x₂ >>= f₁∼f₂)   = whnf≳ x₁∼x₂ >>=W λ x → whnf≳ (f₁∼f₂ x)
    whnf≳ (x ∎)               = reflW x
    whnf≳ (sym {eq = ()} x≅y)
    whnf≳ (x ≅⟨ x≅y ⟩  y≳z)   = trans≅∼W (whnf≅ x≅y) (whnf≳ y≳z)
    whnf≳ (x ≳⟨ x≳y ⟩  y≳z)   = trans≳-W        x≳y  (whnf≳ y≳z)
    whnf≳ (x ≳⟨ x≳y ⟩≅ y≅z)   = trans∼≅W (whnf≳ x≳y) (whnf≅ y≅z)

    -- Another transitivity lemma.

    trans≳≈W : {A : Set} {x y z : A ⊥} →
               RelW (other geq) x y → RelW (other weak) y z →
               RelW (other weak) x z
    trans≳≈W now          now          = now
    trans≳≈W (later  x≳y) (later  y≈z) = later (_ ≳⟨ x≳y ⟩≈ y≈z)
    trans≳≈W (laterˡ x≳y)         y≈z  = laterˡ (trans≳≈W        x≳y  y≈z)
    trans≳≈W         x≳y  (laterʳ y≈z) = laterʳ (trans≳≈W        x≳y  y≈z)
    trans≳≈W (later  x≳y) (laterˡ y≈z) = laterˡ (trans≳≈W (whnf≳ x≳y) y≈z)

    -- All programs can be turned into WHNFs.

    whnf : ∀ {A k} {x y : A ⊥} → RelP k x y → RelW k x y
    whnf now                 = now
    whnf (later  x∼y)        = later     (♭ x∼y)
    whnf (laterʳ x≈y)        = laterʳ (whnf x≈y)
    whnf (laterˡ x∼y)        = laterˡ (whnf x∼y)
    whnf (x₁∼x₂ >>= f₁∼f₂)   = whnf x₁∼x₂ >>=W λ x → whnf (f₁∼f₂ x)
    whnf (x ∎)               = reflW x
    whnf (sym {eq = eq} x≈y) = symW eq (whnf x≈y)
    whnf (x ≅⟨ x≅y ⟩  y∼z)   = trans≅∼W (whnf x≅y) (whnf y∼z)
    whnf (x ≳⟨ x≳y ⟩  y≳z)   = trans≳-W       x≳y  (whnf y≳z)
    whnf (x ≳⟨ x≳y ⟩≅ y≅z)   = trans∼≅W (whnf x≳y) (whnf y≅z)
    whnf (x ≳⟨ x≳y ⟩≈ y≈z)   = trans≳≈W (whnf x≳y) (whnf y≈z)
    whnf (x ≈⟨ x≈y ⟩≅ y≅z)   = trans∼≅W (whnf x≈y) (whnf y≅z)
    whnf (x ≈⟨ x≈y ⟩≲ y≲z)   = symW _ (trans≳≈W (whnf y≲z) (symW _ (whnf x≈y)))

  mutual

    -- Soundness.

    private

      soundW : ∀ {A k} {x y : A ⊥} → RelW k x y → Rel k x y
      soundW now          = now
      soundW (later  x∼y) = later (♯ sound  x∼y)
      soundW (laterʳ x≈y) = laterʳ  (soundW x≈y)
      soundW (laterˡ x∼y) = laterˡ  (soundW x∼y)

    sound : ∀ {A k} {x y : A ⊥} → RelP k x y → Rel k x y
    sound x∼y = soundW (whnf x∼y)

  -- RelP and Rel are equivalent.

  correct : ∀ {A k} {x y : A ⊥} → RelP k x y ⇔ Rel k x y
  correct = equivalent sound complete

------------------------------------------------------------------------
-- Example

module Example where

  open Data.Nat
  open Workaround

  -- McCarthy's f91:

  f91′ : ℕ → ℕ ⊥P
  f91′ n with n ≤? 100
  ... | yes _ = later (♯ (f91′ (11 + n) >>= f91′))
  ... | no  _ = now (n ∸ 10)

  f91 : ℕ → ℕ ⊥
  f91 n = ⟦ f91′ n ⟧P
