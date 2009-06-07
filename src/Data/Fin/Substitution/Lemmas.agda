------------------------------------------------------------------------
-- Substitution lemmas
------------------------------------------------------------------------

module Data.Fin.Substitution.Lemmas where

open import Data.Fin.Substitution
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; lift)
open import Data.Vec
import Data.Vec.Properties as VecProp
open import Data.Function as Fun using (_∘_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning
open import Data.Star using (Star; ε; _◅_; _▻_)

-- A lemma which does not refer to any substitutions.

lift-commutes : ∀ {n} k j (x : Fin (j + (k + n))) →
                lift j suc (lift j (lift k suc) x) ≡
                lift j (lift (suc k) suc) (lift j suc x)
lift-commutes k zero    x       = refl
lift-commutes k (suc j) zero    = refl
lift-commutes k (suc j) (suc x) = cong suc (lift-commutes k j x)

-- The modules below prove a number of substitution lemmas, on the
-- assumption that the underlying substitution machinery satisfies
-- certain properties.

record Lemmas₀ (T : ℕ → Set) : Set where
  field simple : Simple T

  open Simple simple

  extensionality : ∀ {m n} {ρ₁ ρ₂ : Sub T m n} →
                   (∀ x → lookup x ρ₁ ≡ lookup x ρ₂) → ρ₁ ≡ ρ₂
  extensionality {ρ₁ = []}      {[]}       hyp = refl
  extensionality {ρ₁ = t₁ ∷ ρ₁} { t₂ ∷ ρ₂} hyp with hyp zero
  extensionality {ρ₁ = t₁ ∷ ρ₁} {.t₁ ∷ ρ₂} hyp | refl =
    cong (_∷_ t₁) (extensionality (hyp ∘ suc))

  id-↑⋆ : ∀ {n} k → id ↑⋆ k ≡ id {k + n}
  id-↑⋆ zero    = refl
  id-↑⋆ (suc k) = begin
    (id ↑⋆ k) ↑ ≡⟨ cong _↑ (id-↑⋆ k) ⟩
    id        ↑ ∎

  lookup-map-weaken-↑⋆ : ∀ {m n} k x {ρ : Sub T m n} →
                         lookup x (map weaken ρ ↑⋆ k) ≡
                         lookup (lift k suc x) ((ρ ↑) ↑⋆ k)
  lookup-map-weaken-↑⋆ zero    x           = refl
  lookup-map-weaken-↑⋆ (suc k) zero        = refl
  lookup-map-weaken-↑⋆ (suc k) (suc x) {ρ} = begin
    lookup x (map weaken (map weaken ρ ↑⋆ k))        ≡⟨ VecProp.lookup-natural weaken x _ ⟩
    weaken (lookup x (map weaken ρ ↑⋆ k))            ≡⟨ cong weaken (lookup-map-weaken-↑⋆ k x) ⟩
    weaken (lookup (lift k suc x) ((ρ ↑) ↑⋆ k))      ≡⟨ sym (VecProp.lookup-natural weaken (lift k suc x) _) ⟩
    lookup (lift k suc x) (map weaken ((ρ ↑) ↑⋆ k))  ∎

record Lemmas₁ (T : ℕ → Set) : Set where
  field lemmas₀ : Lemmas₀ T

  open Lemmas₀ lemmas₀
  open Simple simple

  field weaken-var : ∀ {n} {x : Fin n} → weaken (var x) ≡ var (suc x)

  lookup-map-weaken : ∀ {m n} x {y} {ρ : Sub T m n} →
                      lookup x             ρ  ≡ var      y →
                      lookup x (map weaken ρ) ≡ var (suc y)
  lookup-map-weaken x {y} {ρ} hyp = begin
    lookup x (map weaken ρ)  ≡⟨ VecProp.lookup-natural weaken x ρ ⟩
    weaken (lookup x ρ)      ≡⟨ cong weaken hyp ⟩
    weaken (var y)           ≡⟨ weaken-var ⟩
    var (suc y)              ∎

  mutual

    lookup-id : ∀ {n} (x : Fin n) → lookup x id ≡ var x
    lookup-id zero    = refl
    lookup-id (suc x) = lookup-wk x

    lookup-wk : ∀ {n} (x : Fin n) → lookup x wk ≡ var (suc x)
    lookup-wk x = lookup-map-weaken x (lookup-id x)

  lookup-↑⋆ : ∀ {m n} (f : Fin m → Fin n) {ρ : Sub T m n} →
              (∀ x → lookup x ρ ≡ var (f x)) →
              ∀ k x → lookup x (ρ ↑⋆ k) ≡ var (lift k f x)
  lookup-↑⋆ f hyp zero    x       = hyp x
  lookup-↑⋆ f hyp (suc k) zero    = refl
  lookup-↑⋆ f hyp (suc k) (suc x) =
    lookup-map-weaken x (lookup-↑⋆ f hyp k x)

  lookup-lift-↑⋆ : ∀ {m n} (f : Fin n → Fin m) {ρ : Sub T m n} →
                   (∀ x → lookup (f x) ρ ≡ var x) →
                   ∀ k x → lookup (lift k f x) (ρ ↑⋆ k) ≡ var x
  lookup-lift-↑⋆ f hyp zero    x       = hyp x
  lookup-lift-↑⋆ f hyp (suc k) zero    = refl
  lookup-lift-↑⋆ f hyp (suc k) (suc x) =
    lookup-map-weaken (lift k f x) (lookup-lift-↑⋆ f hyp k x)

  lookup-wk-↑⋆ : ∀ {n} k (x : Fin (k + n)) →
                 lookup x (wk ↑⋆ k) ≡ var (lift k suc x)
  lookup-wk-↑⋆ = lookup-↑⋆ suc lookup-wk

  lookup-wk-↑⋆-↑⋆ : ∀ {n} k j (x : Fin (j + (k + n))) →
                    lookup x (wk ↑⋆ k ↑⋆ j) ≡
                    var (lift j (lift k suc) x)
  lookup-wk-↑⋆-↑⋆ k = lookup-↑⋆ (lift k suc) (lookup-wk-↑⋆ k)

  lookup-sub-↑⋆ : ∀ {n t} k (x : Fin (k + n)) →
                  lookup (lift k suc x) (sub t ↑⋆ k) ≡ var x
  lookup-sub-↑⋆ = lookup-lift-↑⋆ suc lookup-id

  open Lemmas₀ lemmas₀ public

record Lemmas₂ (T : ℕ → Set) : Set where
  field
    lemmas₁     : Lemmas₁ T
    application : Application T T

  open Lemmas₁ lemmas₁

  subst : Subst T
  subst = record { simple = simple; application = application }

  open Subst subst

  field var-/ : ∀ {m n x} {ρ : Sub T m n} → var x / ρ ≡ lookup x ρ

  suc-/-sub : ∀ {n x} {t : T n} → var (suc x) / sub t ≡ var x
  suc-/-sub {x = x} {t} = begin
    var (suc x) / sub t     ≡⟨ var-/ ⟩
    lookup (suc x) (sub t)  ≡⟨ refl ⟩
    lookup x id             ≡⟨ lookup-id x ⟩
    var x                   ∎

  lookup-⊙ : ∀ {m n k} x {ρ₁ : Sub T m n} {ρ₂ : Sub T n k} →
             lookup x (ρ₁ ⊙ ρ₂) ≡ lookup x ρ₁ / ρ₂
  lookup-⊙ x = VecProp.lookup-natural _ x _

  lookup-⨀ : ∀ {m n} x (ρs : Subs T m n) →
             lookup x (⨀ ρs) ≡ var x /✶ ρs
  lookup-⨀ x ε                = lookup-id x
  lookup-⨀ x (ρ ◅ ε)          = sym var-/
  lookup-⨀ x (ρ ◅ (ρ′ ◅ ρs′)) = begin
    lookup x (⨀ (ρ ◅ ρs))  ≡⟨ refl ⟩
    lookup x (⨀ ρs ⊙ ρ)    ≡⟨ lookup-⊙ x ⟩
    lookup x (⨀ ρs) / ρ    ≡⟨ cong₂ _/_ (lookup-⨀ x ρs) refl ⟩
    var x /✶ ρs / ρ        ∎
    where ρs = ρ′ ◅ ρs′

  id-⊙ : ∀ {m n} {ρ : Sub T m n} → id ⊙ ρ ≡ ρ
  id-⊙ {ρ = ρ} = extensionality λ x → begin
    lookup x (id ⊙ ρ)  ≡⟨ lookup-⊙ x ⟩
    lookup x  id / ρ   ≡⟨ cong₂ _/_ (lookup-id x) refl ⟩
    var x        / ρ   ≡⟨ var-/ ⟩
    lookup x ρ         ∎

  lookup-wk-↑⋆-⊙ : ∀ {m n} k {x} {ρ : Sub T (k + suc m) n} →
                   lookup x (wk ↑⋆ k ⊙ ρ) ≡ lookup (lift k suc x) ρ
  lookup-wk-↑⋆-⊙ k {x} {ρ} = begin
    lookup x (wk ↑⋆ k ⊙ ρ)   ≡⟨ lookup-⊙ x ⟩
    lookup x (wk ↑⋆ k) / ρ   ≡⟨ cong₂ _/_ (lookup-wk-↑⋆ k x) refl ⟩
    var (lift k suc x) / ρ   ≡⟨ var-/ ⟩
    lookup (lift k suc x) ρ  ∎

  wk-⊙-sub′ : ∀ {n} {t : T n} k → wk ↑⋆ k ⊙ sub t ↑⋆ k ≡ id
  wk-⊙-sub′ {t = t} k = extensionality λ x → begin
    lookup x (wk ↑⋆ k ⊙ sub t ↑⋆ k)     ≡⟨ lookup-wk-↑⋆-⊙ k ⟩
    lookup (lift k suc x) (sub t ↑⋆ k)  ≡⟨ lookup-sub-↑⋆ k x ⟩
    var x                               ≡⟨ sym (lookup-id x) ⟩
    lookup x id                         ∎

  wk-⊙-sub : ∀ {n} {t : T n} → wk ⊙ sub t ≡ id
  wk-⊙-sub = wk-⊙-sub′ zero

  var-/-wk-↑⋆ : ∀ {n} k (x : Fin (k + n)) →
                var x / wk ↑⋆ k ≡ var (lift k suc x)
  var-/-wk-↑⋆ k x = begin
    var x / wk ↑⋆ k     ≡⟨ var-/ ⟩
    lookup x (wk ↑⋆ k)  ≡⟨ lookup-wk-↑⋆ k x ⟩
    var (lift k suc x)  ∎

  wk-↑⋆-⊙-wk : ∀ {n} k j →
               wk {n} ↑⋆ k ↑⋆ j ⊙ wk ↑⋆ j ≡
               wk ↑⋆ j ⊙ wk ↑⋆ suc k ↑⋆ j
  wk-↑⋆-⊙-wk k j = extensionality λ x → begin
    lookup x (wk ↑⋆ k ↑⋆ j ⊙ wk ↑⋆ j)               ≡⟨ lookup-⊙ x ⟩
    lookup x (wk ↑⋆ k ↑⋆ j) / wk ↑⋆ j               ≡⟨ cong₂ _/_ (lookup-wk-↑⋆-↑⋆ k j x) refl ⟩
    var (lift j (lift k suc) x) / wk ↑⋆ j           ≡⟨ var-/-wk-↑⋆ j (lift j (lift k suc) x) ⟩
    var (lift j suc (lift j (lift k suc) x))        ≡⟨ cong var (lift-commutes k j x) ⟩
    var (lift j (lift (suc k) suc) (lift j suc x))  ≡⟨ sym (lookup-wk-↑⋆-↑⋆ (suc k) j (lift j suc x)) ⟩
    lookup (lift j suc x) (wk ↑⋆ suc k ↑⋆ j)        ≡⟨ sym var-/ ⟩
    var (lift j suc x) / wk ↑⋆ suc k ↑⋆ j           ≡⟨ cong₂ _/_ (sym (lookup-wk-↑⋆ j x)) refl ⟩
    lookup x (wk ↑⋆ j) / wk ↑⋆ suc k ↑⋆ j           ≡⟨ sym (lookup-⊙ x) ⟩
    lookup x (wk ↑⋆ j ⊙ wk ↑⋆ suc k ↑⋆ j)           ∎

  open Subst   subst   public hiding (simple; application)
  open Lemmas₁ lemmas₁ public

record Lemmas₃ (T : ℕ → Set) : Set where
  field lemmas₂ : Lemmas₂ T

  open Lemmas₂ lemmas₂

  field
    /✶-↑✶ : ∀ {m n} (ρs₁ ρs₂ : Subs T m n) →
            (∀ k x → var x /✶ ρs₁ ↑✶ k ≡ var x /✶ ρs₂ ↑✶ k) →
            ∀ k t → t /✶ ρs₁ ↑✶ k ≡ t /✶ ρs₂ ↑✶ k

  /✶-↑✶′ : ∀ {m n} (ρs₁ ρs₂ : Subs T m n) →
           (∀ k → ⨀ (ρs₁ ↑✶ k) ≡ ⨀ (ρs₂ ↑✶ k)) →
           ∀ k t → t /✶ ρs₁ ↑✶ k ≡ t /✶ ρs₂ ↑✶ k
  /✶-↑✶′ ρs₁ ρs₂ hyp = /✶-↑✶ ρs₁ ρs₂ (λ k x → begin
    var x /✶ ρs₁ ↑✶ k        ≡⟨ sym (lookup-⨀ x (ρs₁ ↑✶ k)) ⟩
    lookup x (⨀ (ρs₁ ↑✶ k))  ≡⟨ cong (lookup x) (hyp k) ⟩
    lookup x (⨀ (ρs₂ ↑✶ k))  ≡⟨ lookup-⨀ x (ρs₂ ↑✶ k) ⟩
    var x /✶ ρs₂ ↑✶ k        ∎)

  id-vanishes : ∀ {n} (t : T n) → t / id ≡ t
  id-vanishes = /✶-↑✶′ (ε ▻ id) ε id-↑⋆ zero

  ⊙-id : ∀ {m n} {ρ : Sub T m n} → ρ ⊙ id ≡ ρ
  ⊙-id {ρ = ρ} = begin
    map (λ t → t / id) ρ  ≡⟨ VecProp.map-cong id-vanishes ρ ⟩
    map Fun.id         ρ  ≡⟨ VecProp.map-id ρ ⟩
    ρ                     ∎

  open Lemmas₂ lemmas₂ public hiding (wk-⊙-sub′)

record Lemmas₄ (T : ℕ → Set) : Set where
  field lemmas₃ : Lemmas₃ T

  open Lemmas₃ lemmas₃

  field /-wk : ∀ {n} {t : T n} → t / wk ≡ weaken t

  private

    ↑-distrib′ : ∀ {m n k} {ρ₁ : Sub T m n} {ρ₂ : Sub T n k} →
                 (∀ t → t / ρ₂ / wk ≡ t / wk / ρ₂ ↑) →
                 (ρ₁ ⊙ ρ₂) ↑ ≡ ρ₁ ↑ ⊙ ρ₂ ↑
    ↑-distrib′ {ρ₁ = ρ₁} {ρ₂} hyp = begin
      (ρ₁ ⊙ ρ₂) ↑                             ≡⟨ refl ⟩
      var zero        ∷ map weaken (ρ₁ ⊙ ρ₂)  ≡⟨ cong₂ _∷_ (sym var-/) lemma ⟩
      var zero / ρ₂ ↑ ∷ map weaken ρ₁ ⊙ ρ₂ ↑  ≡⟨ refl ⟩
      ρ₁ ↑ ⊙ ρ₂ ↑                             ∎
      where
      lemma = begin
        map weaken (map (λ t → t / ρ₂) ρ₁)    ≡⟨ sym (VecProp.map-∘ _ _ _) ⟩
        map (λ t → weaken (t / ρ₂)) ρ₁        ≡⟨ VecProp.map-cong (λ t → begin
                                                   weaken (t / ρ₂)  ≡⟨ sym /-wk ⟩
                                                   t / ρ₂ / wk      ≡⟨ hyp t ⟩
                                                   t / wk / ρ₂ ↑    ≡⟨ cong₂ _/_ /-wk refl ⟩
                                                   weaken t / ρ₂ ↑  ∎) ρ₁ ⟩
        map (λ t → weaken t / ρ₂ ↑) ρ₁        ≡⟨ VecProp.map-∘ _ _ _ ⟩
        map (λ t → t / ρ₂ ↑) (map weaken ρ₁)  ∎

    ↑⋆-distrib′ : ∀ {m n o} {ρ₁ : Sub T m n} {ρ₂ : Sub T n o} →
                  (∀ k t → t / ρ₂ ↑⋆ k / wk ≡ t / wk / ρ₂ ↑⋆ suc k) →
                  ∀ k → (ρ₁ ⊙ ρ₂) ↑⋆ k ≡ ρ₁ ↑⋆ k ⊙ ρ₂ ↑⋆ k
    ↑⋆-distrib′                hyp zero    = refl
    ↑⋆-distrib′ {ρ₁ = ρ₁} {ρ₂} hyp (suc k) = begin
      (ρ₁ ⊙ ρ₂) ↑⋆ suc k         ≡⟨ cong _↑ (↑⋆-distrib′ hyp k) ⟩
      (ρ₁ ↑⋆ k ⊙ ρ₂ ↑⋆ k) ↑      ≡⟨ ↑-distrib′ (hyp k) ⟩
      ρ₁ ↑⋆ suc k ⊙ ρ₂ ↑⋆ suc k  ∎

  map-weaken : ∀ {m n} {ρ : Sub T m n} → map weaken ρ ≡ ρ ⊙ wk
  map-weaken {ρ = ρ} = begin
    map weaken ρ          ≡⟨ VecProp.map-cong (λ _ → sym /-wk) ρ ⟩
    map (λ t → t / wk) ρ  ≡⟨ refl ⟩
    ρ ⊙ wk                ∎

  private

    ⊙-wk′ : ∀ {m n} {ρ : Sub T m n} k →
            ρ ↑⋆ k ⊙ wk ↑⋆ k ≡ wk ↑⋆ k ⊙ ρ ↑ ↑⋆ k
    ⊙-wk′ {ρ = ρ} k = sym (begin
      wk ↑⋆ k ⊙ ρ ↑ ↑⋆ k  ≡⟨ lemma ⟩
      map weaken ρ ↑⋆ k   ≡⟨ cong (λ ρ′ → ρ′ ↑⋆ k) map-weaken ⟩
      (ρ ⊙ wk) ↑⋆ k       ≡⟨ ↑⋆-distrib′ (λ k t →
                               /✶-↑✶′ (ε ▻ wk ↑⋆ k ▻ wk) (ε ▻ wk ▻ wk ↑⋆ suc k)
                                      (wk-↑⋆-⊙-wk k) zero t) k ⟩
      ρ ↑⋆ k ⊙ wk ↑⋆ k    ∎)
      where
      lemma = extensionality λ x → begin
        lookup x (wk ↑⋆ k ⊙ ρ ↑ ↑⋆ k)     ≡⟨ lookup-wk-↑⋆-⊙ k ⟩
        lookup (lift k suc x) (ρ ↑ ↑⋆ k)  ≡⟨ sym (lookup-map-weaken-↑⋆ k x) ⟩
        lookup x (map weaken ρ ↑⋆ k)      ∎

  ⊙-wk : ∀ {m n} {ρ : Sub T m n} → ρ ⊙ wk ≡ wk ⊙ ρ ↑
  ⊙-wk = ⊙-wk′ zero

  wk-commutes : ∀ {m n} {ρ : Sub T m n} t →
                t / ρ / wk ≡ t / wk / ρ ↑
  wk-commutes {ρ = ρ} = /✶-↑✶′ (ε ▻ ρ ▻ wk) (ε ▻ wk ▻ ρ ↑) ⊙-wk′ zero

  ↑⋆-distrib : ∀ {m n o} {ρ₁ : Sub T m n} {ρ₂ : Sub T n o} →
               ∀ k → (ρ₁ ⊙ ρ₂) ↑⋆ k ≡ ρ₁ ↑⋆ k ⊙ ρ₂ ↑⋆ k
  ↑⋆-distrib = ↑⋆-distrib′ (λ _ → wk-commutes)

  /-⊙ : ∀ {m n k} {ρ₁ : Sub T m n} {ρ₂ : Sub T n k} t →
        t / ρ₁ ⊙ ρ₂ ≡ t / ρ₁ / ρ₂
  /-⊙ {ρ₁ = ρ₁} {ρ₂} t =
    /✶-↑✶′ (ε ▻ ρ₁ ⊙ ρ₂) (ε ▻ ρ₁ ▻ ρ₂) ↑⋆-distrib zero t

  ⊙-assoc : ∀ {m n k o}
              {ρ₁ : Sub T m n} {ρ₂ : Sub T n k} {ρ₃ : Sub T k o} →
            ρ₁ ⊙ (ρ₂ ⊙ ρ₃) ≡ (ρ₁ ⊙ ρ₂) ⊙ ρ₃
  ⊙-assoc {ρ₁ = ρ₁} {ρ₂} {ρ₃} = begin
    map (λ t → t / ρ₂ ⊙ ρ₃) ρ₁                  ≡⟨ VecProp.map-cong /-⊙ ρ₁ ⟩
    map (λ t → t / ρ₂ / ρ₃) ρ₁                  ≡⟨ VecProp.map-∘ _ _ _ ⟩
    map (λ t → t / ρ₃) (map (λ t → t / ρ₂) ρ₁)  ∎

  map-weaken-⊙-sub : ∀ {m n} {ρ : Sub T m n} {t} → map weaken ρ ⊙ sub t ≡ ρ
  map-weaken-⊙-sub {ρ = ρ} {t} = begin
    map weaken ρ ⊙ sub t  ≡⟨ cong₂ _⊙_ map-weaken refl ⟩
    ρ ⊙ wk ⊙ sub t        ≡⟨ sym ⊙-assoc ⟩
    ρ ⊙ (wk ⊙ sub t)      ≡⟨ cong (_⊙_ ρ) wk-⊙-sub ⟩
    ρ ⊙ id                ≡⟨ ⊙-id ⟩
    ρ                     ∎

  sub-⊙ : ∀ {m n} {ρ : Sub T m n} t → sub t ⊙ ρ ≡ ρ ↑ ⊙ sub (t / ρ)
  sub-⊙ {ρ = ρ} t = begin
    sub t ⊙ ρ                           ≡⟨ refl ⟩
    t / ρ ∷ id ⊙ ρ                      ≡⟨ cong (_∷_ (t / ρ)) id-⊙ ⟩
    t / ρ ∷ ρ                           ≡⟨ cong (_∷_ (t / ρ)) (sym map-weaken-⊙-sub) ⟩
    t / ρ ∷ map weaken ρ ⊙ sub (t / ρ)  ≡⟨ cong₂ _∷_ (sym var-/) refl ⟩
    ρ ↑ ⊙ sub (t / ρ)                   ∎

  suc-/-↑ : ∀ {m n} {ρ : Sub T m n} x →
            var (suc x) / ρ ↑ ≡ var x / ρ / wk
  suc-/-↑ {ρ = ρ} x = begin
    var (suc x) / ρ ↑        ≡⟨ var-/ ⟩
    lookup x (map weaken ρ)  ≡⟨ cong (lookup x) map-weaken ⟩
    lookup x (ρ ⊙ wk)        ≡⟨ lookup-⊙ x ⟩
    lookup x ρ / wk          ≡⟨ cong₂ _/_ (sym var-/) refl ⟩
    var x / ρ / wk           ∎

  open Lemmas₃ lemmas₃ public
    hiding (/✶-↑✶; /✶-↑✶′; wk-↑⋆-⊙-wk;
            lookup-wk-↑⋆-⊙; lookup-map-weaken-↑⋆)

-- For an example of how AppLemmas can be used, see
-- Data.Fin.Substitution.List.

record AppLemmas (T₁ T₂ : ℕ → Set) : Set where
  field
    application : Application T₁ T₂
    lemmas₄     : Lemmas₄ T₂

  open Application application using (_/_; _/✶_)
  open Lemmas₄ lemmas₄
    using (id; _⊙_; wk; weaken; sub; _↑; ⨀) renaming (_/_ to _⊘_)

  field
    id-vanishes : ∀ {n} (t : T₁ n) → t / id ≡ t
    /-⊙         : ∀ {m n k} {ρ₁ : Sub T₂ m n} {ρ₂ : Sub T₂ n k} t →
                  t / ρ₁ ⊙ ρ₂ ≡ t / ρ₁ / ρ₂

  private module L₄ = Lemmas₄ lemmas₄

  /-⨀ : ∀ {m n} t (ρs : Subs T₂ m n) → t / ⨀ ρs ≡ t /✶ ρs
  /-⨀ t ε                = id-vanishes t
  /-⨀ t (ρ ◅ ε)          = refl
  /-⨀ t (ρ ◅ (ρ′ ◅ ρs′)) = begin
    t / ⨀ ρs ⊙ ρ  ≡⟨ /-⊙ t ⟩
    t / ⨀ ρs / ρ  ≡⟨ cong₂ _/_ (/-⨀ t ρs) refl ⟩
    t /✶ ρs / ρ   ∎
    where ρs = ρ′ ◅ ρs′

  ⨀→/✶ : ∀ {m n} (ρs₁ ρs₂ : Subs T₂ m n) →
         ⨀ ρs₁ ≡ ⨀ ρs₂ → ∀ t → t /✶ ρs₁ ≡ t /✶ ρs₂
  ⨀→/✶ ρs₁ ρs₂ hyp t = begin
    t /✶ ρs₁   ≡⟨ sym (/-⨀ t ρs₁) ⟩
    t / ⨀ ρs₁  ≡⟨ cong (_/_ t) hyp ⟩
    t / ⨀ ρs₂  ≡⟨ /-⨀ t ρs₂ ⟩
    t /✶ ρs₂   ∎

  wk-commutes : ∀ {m n} {ρ : Sub T₂ m n} t →
                t / ρ / wk ≡ t / wk / ρ ↑
  wk-commutes {ρ = ρ} = ⨀→/✶ (ε ▻ ρ ▻ wk) (ε ▻ wk ▻ ρ ↑) L₄.⊙-wk

  sub-commutes : ∀ {m n} {t′} {ρ : Sub T₂ m n} t →
                 t / sub t′ / ρ ≡ t / ρ ↑ / sub (t′ ⊘ ρ)
  sub-commutes {t′ = t′} {ρ} =
    ⨀→/✶ (ε ▻ sub t′ ▻ ρ) (ε ▻ ρ ↑ ▻ sub (t′ ⊘ ρ)) (L₄.sub-⊙ t′)

  wk-sub-vanishes : ∀ {n t′} (t : T₁ n) → t / wk / sub t′ ≡ t
  wk-sub-vanishes {t′ = t′} = ⨀→/✶ (ε ▻ wk ▻ sub t′) ε L₄.wk-⊙-sub

  /-weaken : ∀ {m n} {ρ : Sub T₂ m n} t → t / map weaken ρ ≡ t / ρ / wk
  /-weaken {ρ = ρ} = ⨀→/✶ (ε ▻ map weaken ρ) (ε ▻ ρ ▻ wk) L₄.map-weaken

  open Application application public
  open L₄ public
    hiding (application; _⊙_; _/_; _/✶_;
            id-vanishes; /-⊙; wk-commutes)

record Lemmas₅ (T : ℕ → Set) : Set where
  field lemmas₄ : Lemmas₄ T

  private module L₄ = Lemmas₄ lemmas₄

  appLemmas : AppLemmas T T
  appLemmas = record
    { application = L₄.application
    ; lemmas₄     = lemmas₄
    ; id-vanishes = L₄.id-vanishes
    ; /-⊙         = L₄./-⊙
    }

  open AppLemmas appLemmas public hiding (lemmas₄)

------------------------------------------------------------------------
-- Instantiations and code for facilitating instantiations

-- Lemmas about variable substitutions (renamings).

module VarLemmas where

  open VarSubst

  lemmas₃ : Lemmas₃ Fin
  lemmas₃ = record
    { lemmas₂ = record
      { lemmas₁ = record
        { lemmas₀ = record
          { simple = simple
          }
        ; weaken-var = refl
        }
      ; application = application
      ; var-/       = refl
      }
    ; /✶-↑✶ = λ _ _ hyp → hyp
    }

  private module L₃ = Lemmas₃ lemmas₃

  lemmas₅ : Lemmas₅ Fin
  lemmas₅ = record
    { lemmas₄ = record
      { lemmas₃ = lemmas₃
      ; /-wk    = L₃.lookup-wk _
      }
    }

  open Lemmas₅ lemmas₅ public hiding (lemmas₃)

-- Lemmas about "term" substitutions.

record TermLemmas (T : ℕ → Set) : Set₁ where
  field
    termSubst : TermSubst T

  open TermSubst termSubst

  field
    app-var : ∀ {T′} {lift : Lift T′ T} {m n x} {ρ : Sub T′ m n} →
              app lift (var x) ρ ≡ Lift.lift lift (lookup x ρ)
    /✶-↑✶   : ∀ {T₁ T₂} {lift₁ : Lift T₁ T} {lift₂ : Lift T₂ T} →
              let open Lifted lift₁
                    using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
                  open Lifted lift₂
                    using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)
              in
              ∀ {m n} (ρs₁ : Subs T₁ m n) (ρs₂ : Subs T₂ m n) →
              (∀ k x → var x /✶₁ ρs₁ ↑✶₁ k ≡ var x /✶₂ ρs₂ ↑✶₂ k) →
              ∀ k t → t /✶₁ ρs₁ ↑✶₁ k ≡ t /✶₂ ρs₂ ↑✶₂ k

  private module V = VarLemmas

  lemmas₃ : Lemmas₃ T
  lemmas₃ = record
    { lemmas₂ = record
      { lemmas₁ = record
        { lemmas₀ = record
          { simple = simple
          }
        ; weaken-var = λ {_ x} → begin
            var x /Var V.wk      ≡⟨ app-var ⟩
            var (lookup x V.wk)  ≡⟨ cong var (V.lookup-wk x) ⟩
            var (suc x)          ∎
        }
      ; application = Subst.application subst
      ; var-/       = app-var
      }
    ; /✶-↑✶ = /✶-↑✶
    }

  private module L₃ = Lemmas₃ lemmas₃

  lemmas₅ : Lemmas₅ T
  lemmas₅ = record
    { lemmas₄ = record
      { lemmas₃ = lemmas₃
      ; /-wk    = λ {_ t} → begin
          t / wk       ≡⟨ /✶-↑✶ (ε ▻ wk) (ε ▻ V.wk)
                            (λ k x → begin
                               var x / wk ↑⋆ k                 ≡⟨ L₃.var-/-wk-↑⋆ k x ⟩
                               var (lift k suc x)              ≡⟨ cong var (sym (V.var-/-wk-↑⋆ k x)) ⟩
                               var (lookup x (V._↑⋆_ V.wk k))  ≡⟨ sym app-var ⟩
                               var x /Var V._↑⋆_ V.wk k        ∎)
                            zero t ⟩
          t /Var V.wk  ≡⟨ refl ⟩
          weaken t     ∎
      }
    }

  open Lemmas₅ lemmas₅ public hiding (lemmas₃)
