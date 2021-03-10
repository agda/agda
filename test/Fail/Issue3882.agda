{-# OPTIONS --rewriting #-}

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  instance refl : x ≡ x

{-# BUILTIN REWRITE _≡_ #-}

postulate
  admit : ∀ {ℓ} {A : Set ℓ} → A
  X : Set

postulate
  Wrap : Set → Set

  wrap : {A : Set} → A → Wrap A

  rec : (A : Set) (P : Set) → (A → P) → Wrap A → P

  Rec : (A : Set) (P : Set₁) → (A → P) → Wrap A → P

  Rec-β : {A : Set} (P : Set₁) → ∀ f → (a : A) → Rec A P f (wrap a) ≡ f a

  {-# REWRITE Rec-β #-} -- bug disappears without this

record Σ {ℓ} (A : Set ℓ) (B : A → Set) : Set ℓ where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

-- bug disappears if Comp or isFib is not wrapped in a record

record Comp (A : X → Set) : Set where
  field
    comp : ∀ s → A s

open Comp public

record isFib {Γ : Set} (A : Γ → Set) : Set where
  field
    lift : (p : X → Γ) → Comp (λ x → A (p x))

open isFib public

compSys : (ψ : X → Set)
  (A : Σ X (λ x → Wrap (ψ x)) → Set)
  (u : ∀ s → Wrap (ψ s)) (s : X)
  → A (s , u s)
compSys ψ A u s =
  rec (∀ i → ψ i) (A (s , u s))
    (λ v →
      subst (λ s → wrap (v s)) (λ s → u s) admit
      .lift (λ s → s) .comp s)
    admit
  where
  subst : (w w' : ∀ i → Wrap (ψ i)) → isFib (λ s → A (s , w s)) → isFib (λ s → A (s , w' s))
  subst = admit

-- bug disappears if ×id is inlined
×id : {A A' : Set} {B : A' → Set} (f : A → A') → Σ A (λ x → B (f x)) → Σ A' B
×id f (a , b) = (f a , b)

fib : (ψ : X → Set) (A : Σ X (λ x → Wrap (ψ x)) → Set) → isFib A
fib ψ A .lift p .comp =
  compSys (λ x → ψ (p x .fst)) (λ xu → A (×id (λ x → p x .fst) xu)) (λ x → p x .snd)

-- bug seems to disappear if the underscore in (Σ Set _) is filled in
template : (ψ : X → Set) → X → Σ (Σ X (λ x → Wrap (ψ x)) → Set) isFib
template ψ n =
  (_ , fib ψ (λ b → Rec (ψ (b .fst)) (Σ Set _) (λ _ → admit) (b .snd) .fst))

eq : {B : Set₁} (f : X → B) {x y : X} → f x ≡ f y
eq = admit

templateEq : (ψ : X → Set) (n₀ : X) → template ψ n₀ ≡ template ψ n₀
templateEq ψ n₀ = eq (template ψ)
