------------------------------------------------------------------------
-- The partiality monad
------------------------------------------------------------------------

module Category.Monad.Partiality where

open import Coinduction
open import Category.Monad
open import Data.Bool
open import Data.Nat
open import Data.Product as Prod
open import Data.Sum
open import Function
open import Function.Equivalence using (_⇔_; equivalent)
open import Relation.Binary
open import Relation.Nullary
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
  later x >>= f = later (♯ ♭ x >>= f)

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
-- Equality

-- The partiality monad comes with two forms of equality: weak and
-- strong.

data Kind : Set where
  weak strong : Kind

mutual

  infix 4 _≅_ _≈_

  _≅_ : {A : Set} → A ⊥ → A ⊥ → Set
  _≅_ = Eq strong

  _≈_ : {A : Set} → A ⊥ → A ⊥ → Set
  _≈_ = Eq weak

  data Eq {A : Set} : Kind → A ⊥ → A ⊥ → Set where
    now    : ∀ {k v}                                 → Eq k (now   v) (now   v)
    later  : ∀ {k x y} (x≈y : ∞ (Eq k (♭ x)  (♭ y))) → Eq k (later x) (later y)
    laterʳ : ∀ {x y}   (x≈y :            x  ≈ ♭ y  ) →             x ≈ later y
    laterˡ : ∀ {x y}   (x≈y :          ♭ x  ≈   y  ) →       later x ≈       y

-- Weak equality includes the strong one.

≅⇒≈ : {A : Set} {x y : A ⊥} → x ≅ y → x ≈ y
≅⇒≈ now         = now
≅⇒≈ (later x≅y) = later (♯ ≅⇒≈ (♭ x≅y))

-- The two equalities agree for non-terminating computations.

≈never⇒≅never : {A : Set} {x : A ⊥} → x ≈ never → x ≅ never
≈never⇒≅never (later  x≈never) = later (♯ ≈never⇒≅never (♭ x≈never))
≈never⇒≅never (laterʳ x≈never) =          ≈never⇒≅never    x≈never
≈never⇒≅never (laterˡ x≈never) = later (♯ ≈never⇒≅never    x≈never)

-- Later can be dropped.

laterʳ⁻¹ : ∀ {A : Set} {x : A ⊥} {y} → x ≈ later y → x ≈ ♭ y
laterʳ⁻¹ (later  x≈y)  = laterˡ        (♭ x≈y)
laterʳ⁻¹ (laterʳ x≈y)  = x≈y
laterʳ⁻¹ (laterˡ x≈ly) = laterˡ (laterʳ⁻¹ x≈ly)

laterˡ⁻¹ : ∀ {A : Set} {x} {y : A ⊥} → later x ≈ y → ♭ x ≈ y
laterˡ⁻¹ (later  x≈y)  = laterʳ         (♭ x≈y)
laterˡ⁻¹ (laterʳ lx≈y) = laterʳ (laterˡ⁻¹ lx≈y)
laterˡ⁻¹ (laterˡ x≈y)  = x≈y

later⁻¹ : ∀ {A : Set} {k} {x y : ∞ (A ⊥)} →
          Eq k (later x) (later y) → Eq k (♭ x) (♭ y)
later⁻¹ {k = weak}       lx≈ly = laterˡ⁻¹ (laterʳ⁻¹ lx≈ly)
later⁻¹            (later x≈y) = ♭ x≈y

-- Both equalities are equivalences.

setoid : Set → Kind → Setoid _ _
setoid A k = record
  { Carrier       = A ⊥
  ; _≈_           = Eq k
  ; isEquivalence = record {refl = refl _; sym = sym; trans = trans}
  }
  where
  refl : (x : A ⊥) → Eq k x x
  refl (now v)   = now
  refl (later x) = later (♯ refl (♭ x))

  sym : ∀ {k} {x y : A ⊥} → Eq k x y → Eq k y x
  sym now          = now
  sym (later  x≈y) = later (♯ sym (♭ x≈y))
  sym (laterʳ x≈y) = laterˡ (sym x≈y)
  sym (laterˡ x≈y) = laterʳ (sym x≈y)

  trans : ∀ {k} {x y z : A ⊥} → Eq k x y → Eq k y z → Eq k x z
  trans {x = now v} {z = z} p q = tr p q
    where
    tr : ∀ {k y} → Eq k (now v) y → Eq k y z → Eq k (now v) z
    tr now          y≈z  = y≈z
    tr (laterʳ v≈y) ly≈z = tr v≈y (laterˡ⁻¹ ly≈z)
  trans {x = later x} lx≈y y≈z = tr lx≈y y≈z
    where
    tr : ∀ {k y z} → Eq k (later x) y → Eq k y z → Eq k (later x) z
    tr (later   x≈y) (later  y≈z) = later  (♯ trans         (♭ x≈y) (♭ y≈z))
    tr (laterʳ lx≈y) (later  y≈z) = later  (♯ trans (laterˡ⁻¹ lx≈y) (♭ y≈z))
    tr         lx≈y  (laterʳ y≈z) = later  (♯ trans (laterˡ⁻¹ lx≈y)    y≈z )
    tr         lx≈ly (laterˡ y≈z) =           tr    (laterʳ⁻¹ lx≈ly)   y≈z
    tr (laterˡ  x≈y)         y≈z  = laterˡ (  trans            x≈y     y≈z )

private module S {A : Set} {k} = Setoid (setoid A k)

-- Now is not never.

now≉never : {A : Set} {x : A} → ¬ now x ≈ never
now≉never (laterʳ hyp) = now≉never hyp

-- A partial value is either now or never (classically).

now-or-never : {A : Set} (x : A ⊥) →
               ¬ ¬ ((∃ λ y → x ≈ now y) ⊎ x ≈ never)
now-or-never {A} x = helper <$> excluded-middle
  where
  open RawMonad ¬¬-Monad

  not-now-is-never : (x : A ⊥) → (∄ λ y → x ≈ now y) → x ≈ never
  not-now-is-never (now x)   hyp with hyp (, now)
  ... | ()
  not-now-is-never (later x) hyp =
    later (♯ not-now-is-never (♭ x) (hyp ∘ Prod.map id laterˡ))

  helper : Dec (∃ λ y → x ≈ now y) → _
  helper (yes ≈now) = inj₁ ≈now
  helper (no  ≉now) = inj₂ $ not-now-is-never x ≉now

-- Bind preserves equality.

_>>=-cong_ :
  ∀ {A B : Set} {k} {x₁ x₂ : A ⊥} {f₁ f₂ : A → B ⊥} → let open M in
  Eq k x₁ x₂ → (∀ x → Eq k (f₁ x) (f₂ x)) → Eq k (x₁ >>= f₁) (x₂ >>= f₂)
now          >>=-cong f₁≈f₂ = f₁≈f₂ _
later  x₁≈x₂ >>=-cong f₁≈f₂ = later (♯ (♭ x₁≈x₂ >>=-cong f₁≈f₂))
laterʳ x₁≈x₂ >>=-cong f₁≈f₂ = laterʳ (x₁≈x₂ >>=-cong f₁≈f₂)
laterˡ x₁≈x₂ >>=-cong f₁≈f₂ = laterˡ (x₁≈x₂ >>=-cong f₁≈f₂)

-- Inversion lemmas for bind.

>>=-inversion-⇓ : ∀ {A B : Set} {k} x {f : A → B ⊥} {y} → let open M in
                  Eq k (x >>= f) (now y) →
                  ∃ λ z → Eq k x (now z) × Eq k (f z) (now y)
>>=-inversion-⇓ (now   x) ≈now          = (x , now , ≈now)
>>=-inversion-⇓ (later x) (laterˡ ≈now) =
  Prod.map id (Prod.map laterˡ id) $ >>=-inversion-⇓ (♭ x) ≈now

>>=-inversion-⇑ : ∀ {A B : Set} x {f : A → B ⊥} → let open M in
                  (x >>= f) ≈ never →
                  ¬ ¬ (x ≈ never ⊎ ∃ λ y → x ≈ now y × f y ≈ never)
>>=-inversion-⇑ {A} x {f} ≈never = helper <$> now-or-never x
  where
  open RawMonad ¬¬-Monad using (_<$>_)
  open M using (_>>=_)

  is-never : ∀ {x y} → x ≈ now y → (x >>= f) ≈ never → f y ≈ never
  is-never now           = id
  is-never (laterˡ ≈now) = is-never ≈now ∘ later⁻¹

  helper : (∃ λ y → x ≈ now y) ⊎ x ≈ never → _
  helper (inj₁ (y , ≈now)) = inj₂ (y , ≈now , is-never ≈now ≈never)
  helper (inj₂ ≈never)     = inj₁ ≈never

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
-- An alternative, but equivalent, formulation of equality

module AlternativeEquality where

  mutual

    infix  4 _≅P_ _≈P_
    infix  2 _∎
    infixr 2 _≅⟨_⟩_ _≈⟨_⟩_
    infixl 1 _>>=_

    -- Equality proof "programs".

    _≅P_ : {A : Set} → A ⊥ → A ⊥ → Set₁
    _≅P_ = EqP strong

    _≈P_ : {A : Set} → A ⊥ → A ⊥ → Set₁
    _≈P_ = EqP weak

    data EqP {A : Set} : Kind → A ⊥ → A ⊥ → Set₁ where

      -- Congruences.

      now   : ∀ {k v} → EqP k (now v) (now v)
      later : ∀ {k x y} (x≈y : ∞ (EqP k (♭ x) (♭ y))) →
              EqP k (later x) (later y)
      _>>=_ : ∀ {B : Set} {k} {x₁ x₂} {f₁ f₂ : B → A ⊥} → let open M in
              (x₁≈x₂ : EqP k x₁ x₂) (f₁≈f₂ : ∀ x → EqP k (f₁ x) (f₂ x)) →
              EqP k (x₁ >>= f₁) (x₂ >>= f₂)

      -- Weak equality.

      laterʳ : ∀ {x y} (x≈y :   x ≈P ♭ y) →       x ≈P later y
      laterˡ : ∀ {x y} (x≈y : ♭ x ≈P   y) → later x ≈P       y

      -- Equational reasoning. Note that including full transitivity
      -- for weak equality would make EqP weak trivial. Instead a
      -- limited notion of transitivity, similar to weak bisimulation
      -- up-to strong bisimulation, is included.

      _∎     : ∀ x → x ≅P x
      sym    : ∀ {k x y} (x≈y : EqP k x y) → EqP k y x
      _≅⟨_⟩_ : ∀ {k} x {y z} (x≅y : x ≅P y) (y≈z : EqP k y z) → EqP k x z
      _≈⟨_⟩_ : ∀     x {y z} (x≈y : x ≈P y) (y≅z : y ≅P z) → x ≈P z

  -- EqP is complete with respect to Eq.

  completeP : ∀ {A : Set} {k} {x y : A ⊥} → Eq k x y → EqP k x y
  completeP now          = now
  completeP (later  x≈y) = later (♯ completeP (♭ x≈y))
  completeP (laterʳ x≈y) = laterʳ  (completeP    x≈y)
  completeP (laterˡ x≈y) = laterˡ  (completeP    x≈y)

  -- EqP is sound with respect to Eq.

  private

    -- Equality proof WHNFs.

    data EqW {A : Set} : Kind → A ⊥ → A ⊥ → Set₁ where
      now    : ∀ {k v}                                 → EqW k    (now   v) (now   v)
      later  : ∀ {k x y} (x≈y : EqP  k    (♭ x) (♭ y)) → EqW k    (later x) (later y)
      laterʳ : ∀ {x y}   (x≈y : EqW weak    x  (♭ y) ) → EqW weak        x  (later y)
      laterˡ : ∀ {x y}   (x≈y : EqW weak (♭ x)    y  ) → EqW weak (later x)        y

    -- WHNFs can be turned into programs.

    program : ∀ {A : Set} {k} {x y : A ⊥} → EqW k x y → EqP k x y
    program now          = now
    program (later  x≈y) = later (♯ x≈y)
    program (laterˡ x≈y) = laterˡ (program x≈y)
    program (laterʳ x≈y) = laterʳ (program x≈y)

    -- Lemmas for WHNFs.

    _>>=W_ :
      ∀ {A B : Set} {k} {x₁ x₂} {f₁ f₂ : B → A ⊥} →
      EqW k x₁ x₂ → (∀ x → EqW k (f₁ x) (f₂ x)) →
      EqW k (M._>>=_ x₁ f₁) (M._>>=_ x₂ f₂)
    now        >>=W f₁≈f₂ = f₁≈f₂ _
    later  x≈y >>=W f₁≈f₂ = later  (x≈y >>= program ∘ f₁≈f₂)
    laterʳ x≈y >>=W f₁≈f₂ = laterʳ (x≈y >>=W f₁≈f₂)
    laterˡ x≈y >>=W f₁≈f₂ = laterˡ (x≈y >>=W f₁≈f₂)

    reflW : {A : Set} (x : A ⊥) → EqW strong x x
    reflW (now   x) = now
    reflW (later x) = later (♭ x ∎)

    symW : ∀ {A : Set} {k} {x y : A ⊥} → EqW k x y → EqW k y x
    symW now          = now
    symW (later  x≈y) = later  (sym  x≈y)
    symW (laterʳ x≈y) = laterˡ (symW x≈y)
    symW (laterˡ x≈y) = laterʳ (symW x≈y)

    transW : ∀ {A : Set} {x y z : A ⊥} →
             EqW strong x y → EqW strong y z → EqW strong x z
    transW now                y≈z  = y≈z
    transW (later x≅y) (later y≈z) = later (_ ≅⟨ x≅y ⟩ y≈z)

    -- Strong equality programs can be turned into WHNFs.

    whnfS : ∀ {A} {x y : A ⊥} → x ≅P y → EqW strong x y
    whnfS now               = now
    whnfS (later x≈y)       = later (♭ x≈y)
    whnfS (x₁≈x₂ >>= f₁≈f₂) = whnfS x₁≈x₂ >>=W λ x → whnfS (f₁≈f₂ x)
    whnfS (x ∎)             = reflW x
    whnfS (sym x≈y)         = symW (whnfS x≈y)
    whnfS (x ≅⟨ x≅y ⟩ y≈z)  = transW (whnfS x≅y) (whnfS y≈z)

    -- More lemmas for WHNFs.

    transˡ : ∀ {A : Set} {k} {x y z : A ⊥} →
             EqW strong x y → EqW k y z → EqW k x z
    transˡ now                  y≈z  = y≈z
    transˡ (later x≅y) (later   y≈z) = later (_ ≅⟨ x≅y ⟩ y≈z)
    transˡ        x≅y  (laterʳ ly≈z) = laterʳ (transˡ x≅y ly≈z)
    transˡ (later x≅y) (laterˡ  y≈z) = laterˡ (transˡ (whnfS x≅y) y≈z)

    transʳ : ∀ {A : Set} {x y z : A ⊥} →
             EqW weak x y → EqW strong y z → EqW weak x z
    transʳ x≈y y≈z = symW (transˡ (symW y≈z) (symW x≈y))

    -- All equality programs can be turned into WHNFs.

    whnf : ∀ {A k} {x y : A ⊥} → EqP k x y → EqW k x y
    whnf now               = now
    whnf (later  x≈y)      = later     (♭ x≈y)
    whnf (laterʳ x≈y)      = laterʳ (whnf x≈y)
    whnf (laterˡ x≈y)      = laterˡ (whnf x≈y)
    whnf (x₁≈x₂ >>= f₁≈f₂) = whnf x₁≈x₂ >>=W λ x → whnf (f₁≈f₂ x)
    whnf (x ∎)             = reflW x
    whnf (sym x≈y)         = symW (whnf x≈y)
    whnf (x ≅⟨ x≅y ⟩ y≈z)  = transˡ (whnf x≅y) (whnf y≈z)
    whnf (x ≈⟨ x≈y ⟩ y≅z)  = transʳ (whnf x≈y) (whnf y≅z)

  mutual

    -- Soundness.

    private

      soundW : ∀ {A k} {x y : A ⊥} → EqW k x y → Eq k x y
      soundW now          = now
      soundW (later  x≈y) = later (♯ soundP x≈y)
      soundW (laterʳ x≈y) = laterʳ  (soundW x≈y)
      soundW (laterˡ x≈y) = laterˡ  (soundW x≈y)

    soundP : ∀ {A k} {x y : A ⊥} → EqP k x y → Eq k x y
    soundP x≈y = soundW (whnf x≈y)

  -- Correctness.

  correct : ∀ {A k} {x y : A ⊥} → EqP k x y ⇔ Eq k x y
  correct = equivalent soundP completeP

------------------------------------------------------------------------
-- Examples

module Examples where

  open import Relation.Nullary
  open Workaround

  -- McCarthy's f91:

  f91′ : ℕ → ℕ ⊥P
  f91′ n with n ≤? 100
  ... | yes _ = later (♯ (f91′ (11 + n) >>= f91′))
  ... | no  _ = now (n ∸ 10)

  f91 : ℕ → ℕ ⊥
  f91 n = ⟦ f91′ n ⟧P
