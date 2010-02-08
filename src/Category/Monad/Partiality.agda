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

infix 4 _≈_

data _≈_ {A : Set} : A ⊥ → A ⊥ → Set where
  now    : ∀ {v}                         → now   v ≈ now   v
  later  : ∀ {x y} (x≈y : ∞ (♭ x ≈ ♭ y)) → later x ≈ later y
  laterʳ : ∀ {x y} (x≈y :      x ≈ ♭ y ) →       x ≈ later y
  laterˡ : ∀ {x y} (x≈y :    ♭ x ≈   y ) → later x ≈       y

-- Later can be dropped.

laterʳ⁻¹ : ∀ {A : Set} {x : A ⊥} {y} → x ≈ later y → x ≈ ♭ y
laterʳ⁻¹ (later  x≈y)  = laterˡ        (♭ x≈y)
laterʳ⁻¹ (laterʳ x≈y)  = x≈y
laterʳ⁻¹ (laterˡ x≈ly) = laterˡ (laterʳ⁻¹ x≈ly)

laterˡ⁻¹ : ∀ {A : Set} {x} {y : A ⊥} → later x ≈ y → ♭ x ≈ y
laterˡ⁻¹ (later  x≈y)  = laterʳ         (♭ x≈y)
laterˡ⁻¹ (laterʳ lx≈y) = laterʳ (laterˡ⁻¹ lx≈y)
laterˡ⁻¹ (laterˡ x≈y)  = x≈y

later⁻¹ : ∀ {A : Set} {x y : ∞ (A ⊥)} → later x ≈ later y → ♭ x ≈ ♭ y
later⁻¹ = laterˡ⁻¹ ∘ laterʳ⁻¹

-- _≈_ is an equivalence relation.

setoid : Set → Setoid _ _
setoid A = record
  { Carrier       = A ⊥
  ; _≈_           = _≈_
  ; isEquivalence = record {refl = refl _; sym = sym; trans = trans}
  }
  where
  refl : (x : A ⊥) → x ≈ x
  refl (now v)   = now
  refl (later x) = later (♯ refl (♭ x))

  sym : {x y : A ⊥} → x ≈ y → y ≈ x
  sym now          = now
  sym (later  x≈y) = later (♯ sym (♭ x≈y))
  sym (laterʳ x≈y) = laterˡ (sym x≈y)
  sym (laterˡ x≈y) = laterʳ (sym x≈y)

  trans : {x y z : A ⊥} → x ≈ y → y ≈ z → x ≈ z
  trans {x = now v} {z = z} p q = tr p q
    where
    tr : ∀ {y} → now v ≈ y → y ≈ z → now v ≈ z
    tr now          y≈z  = y≈z
    tr (laterʳ v≈y) ly≈z = tr v≈y (laterˡ⁻¹ ly≈z)
  trans {x = later x} lx≈y y≈z = tr lx≈y y≈z
    where
    tr : ∀ {y z} → later x ≈ y → y ≈ z → later x ≈ z
    tr         lx≈ly (later  y≈z) = later  (♯ trans (laterˡ⁻¹ lx≈ly) (laterˡ (♭ y≈z)))
    tr         lx≈y  (laterʳ y≈z) = later  (♯ trans (laterˡ⁻¹ lx≈y)             y≈z  )
    tr         lx≈ly (laterˡ y≈z) =           tr    (laterʳ⁻¹ lx≈ly)            y≈z
    tr (laterˡ  x≈y)         y≈z  = laterˡ (  trans            x≈y              y≈z  )

private module S {A : Set} = Setoid (setoid A)

-- Now is not never.

now≉never : {A : Set} {x : A} → ¬ (now x ≈ never)
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

_>>=-cong_ : {A B : Set} {x₁ x₂ : A ⊥} {f₁ f₂ : A → B ⊥} → let open M in
             x₁ ≈ x₂ → (∀ x → f₁ x ≈ f₂ x) → (x₁ >>= f₁) ≈ (x₂ >>= f₂)
now          >>=-cong f₁≈f₂ = f₁≈f₂ _
later  x₁≈x₂ >>=-cong f₁≈f₂ = later (♯ (♭ x₁≈x₂ >>=-cong f₁≈f₂))
laterʳ x₁≈x₂ >>=-cong f₁≈f₂ = laterʳ (x₁≈x₂ >>=-cong f₁≈f₂)
laterˡ x₁≈x₂ >>=-cong f₁≈f₂ = laterˡ (x₁≈x₂ >>=-cong f₁≈f₂)

-- Inversion lemmas for bind.

>>=-inversion-⇓ : ∀ {A B : Set} x {f : A → B ⊥} {y} → let open M in
                  (x >>= f) ≈ now y → ∃ λ z → x ≈ now z × f z ≈ now y
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
            (never >>= f) ≈ never
left-zero f = later (♯ left-zero f)

right-zero : {A B : Set} (x : A ⊥) → let open M in
             (x >>= λ _ → never) ≈ never {A = B}
right-zero (now   x) = S.refl
right-zero (later x) = later (♯ right-zero (♭ x))

-- Now is a left and right identity of bind.

left-identity : {A B : Set} (x : A) (f : A → B ⊥) → let open M in
                (now x >>= f) ≈ f x
left-identity x f = S.refl

right-identity : {A : Set} (x : A ⊥) → let open M in
                 (x >>= now) ≈ x
right-identity (now   x) = now
right-identity (later x) = later (♯ right-identity (♭ x))

-- Bind is associative.

associative : {A B C : Set} (x : A ⊥) (f : A → B ⊥) (g : B → C ⊥) →
              let open M in
              (x >>= f >>= g) ≈ (x >>= λ y → f y >>= g)
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

  now-hom : ∀ {A} (x : A) → ⟦ now x ⟧P ≈ now x
  now-hom _ = S.refl

  later-hom : ∀ {A} (x : ∞ (A ⊥P)) →
              ⟦ later x ⟧P ≈ later (♯ ⟦ ♭ x ⟧P)
  later-hom x = later (♯ S.refl)

  mutual

    private

      >>=-homW : ∀ {A B} (x : A ⊥W) (f : A → B ⊥P) →
                 ⟦ x >>=W f ⟧W ≈ M._>>=_ ⟦ x ⟧W (λ y → ⟦ f y ⟧P)
      >>=-homW (now   x) f = S.refl
      >>=-homW (later x) f = later (♯ >>=-hom x f)

    >>=-hom : ∀ {A B} (x : A ⊥P) (f : A → B ⊥P) →
              ⟦ x >>= f ⟧P ≈ M._>>=_ ⟦ x ⟧P (λ y → ⟦ f y ⟧P)
    >>=-hom x f = >>=-homW (whnf x) f

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
