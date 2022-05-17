{-# OPTIONS --cubical-compatible --rewriting --confluence-check #-}

open import Agda.Primitive using (Level; _⊔_; Setω; lzero; lsuc)

module Issue4032 where

infix 4 _≡_

data _≡_ {ℓ : Level} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : a ≡ a

{-# BUILTIN REWRITE _≡_ #-}

run : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
run refl x = x

nur : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → B → A
nur refl x = x

convert : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) (a : A) → nur p (run p a) ≡ a
convert refl a = refl

trevnoc : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) (b : B) → run p (nur p b) ≡ b
trevnoc refl b = refl

ap : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {a₁ a₂} → a₁ ≡ a₂ → f a₁ ≡ f a₂
ap f refl = refl

transport : ∀ {a b} {A : Set a} (B : A → Set b) {x y : A} (p : x ≡ y) → B x → B y
transport B p = run (ap B p)

apD : ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) {a₁ a₂} → (p : a₁ ≡ a₂) → transport B p (f a₁) ≡ f a₂
apD f refl = refl

ap2 : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c} (f : (x : A) → B x → C) {a₁ a₂} (pa : a₁ ≡ a₂) {b₁ b₂} → transport B pa b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
ap2 f refl refl = refl

postulate fromIso : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (g : B → A) (η : (x : A) → g (f x) ≡ x) (ε : (x : B) → f (g x) ≡ x) (τ : (x : A) → ap f (η x) ≡ ε (f x)) → A ≡ B
postulate fromIso-refl : ∀ {ℓ} {A : Set ℓ} → fromIso {ℓ} {A} {A} (λ x → x) (λ x → x) (λ x → refl) (λ x → refl) (λ x → refl) ≡ refl
{-# REWRITE fromIso-refl #-}

J : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {a : A} (P : (b : A) → a ≡ b → Set ℓ₂) {b : A} (p : a ≡ b) → P a refl → P b p
J R refl r = r

module foo {-ℓ₁-} {ℓ} {Γ : Set ℓ{-₁-}} {xs ys : Γ} (ps : xs ≡ ys) (tA : Γ → Set ℓ) (tB : (γ : Γ) → tA γ → Set ℓ) where
  module pf where
    iso-f : ((a : tA xs) → (tB xs) a) → ((a : tA ys) → (tB ys) a)
    iso-f var1 var0 = run (ap2 tB ps (trevnoc (ap tA ps) var0)) (var1 (nur (ap tA ps) var0))

    iso-g : ((a : tA ys) → (tB ys) a) → ((a : tA xs) → (tB xs) a)
    iso-g var1 var0 = nur (ap2 tB ps refl) (var1 (run (ap tA ps) var0))

    iso-η : (var0 : _) → iso-g (iso-f var0) ≡ var0
    iso-η var0 = J (λ ys (ps : xs ≡ ys) → (λ var1 → nur (ap2 tB ps refl) (run (ap2 tB ps (trevnoc (ap tA ps) (run (ap tA ps) var1))) (var0 (nur (ap tA ps) (run (ap tA ps) var1))))) ≡ var0) ps refl

    iso-ε : (var0 : _) → iso-f (iso-g var0) ≡ var0
    iso-ε = J (λ ys (ps : xs ≡ ys) → (var0 : (a : tA ys) → tB ys a) → (λ var1 → run (ap2 tB ps (trevnoc (ap tA ps) var1)) (nur (ap2 tB ps refl) (var0 (run (ap tA ps) (nur (ap tA ps) var1))))) ≡ var0) ps (λ var0 → refl)
    iso-τ : (var0 : _) → ap iso-f (iso-η var0) ≡ iso-ε (iso-f var0)
    iso-τ var0 = J
                   (λ ys (ps : xs ≡ ys) →
                      ap
                      (λ var1 var2 →
                         run (ap2 tB ps (trevnoc (ap tA ps) var2))
                         (var1 (nur (ap tA ps) var2)))
                      (J
                       (λ ys₁ ps₁ →
                          (λ var1 →
                             nur (ap2 tB ps₁ refl)
                             (run (ap2 tB ps₁ (trevnoc (ap tA ps₁) (run (ap tA ps₁) var1)))
                              (var0 (nur (ap tA ps₁) (run (ap tA ps₁) var1)))))
                          ≡ var0)
                       ps refl)
                      ≡
                      J
                      (λ ys₁ ps₁ →
                         (var1 : (a : tA ys₁) → tB ys₁ a) →
                         (λ var2 →
                            run (ap2 tB ps₁ (trevnoc (ap tA ps₁) var2))
                            (nur (ap2 tB ps₁ refl)
                             (var1 (run (ap tA ps₁) (nur (ap tA ps₁) var2)))))
                         ≡ var1)
                      ps (λ var1 → refl)
                      (λ var1 →
                         run (ap2 tB ps (trevnoc (ap tA ps) var1))
                         (var0 (nur (ap tA ps) var1))))
                   ps refl

  open pf

  pf : ((a : tA xs) → (tB xs) a) ≡ ((a : tA ys) → (tB ys) a)
  pf = fromIso iso-f iso-g iso-η iso-ε iso-τ

module bar {ℓ} {Γ : Set ℓ} {γ : Γ} {A : Γ → Set ℓ} {B : (γ : Γ) → A γ → Set ℓ} where
  g1 : ((a : A γ) → B γ a) → (a : A γ) → B γ a
  g2 : ((a : A γ) → B γ a) → (a : A γ) → B γ a

  g1 = foo.pf.iso-g {xs = γ} refl A B
  g2 = λ f x → f x

  pfg : g1 ≡ g2
  pfg = refl

  baz : foo.pf {xs = γ} refl A B ≡ refl
  baz = pf
    where
      pf : fromIso {_} {(x : A γ) → B γ x} (λ f x → f x) g2 (foo.pf.iso-η refl A B) (foo.pf.iso-ε refl A B) (foo.pf.iso-τ refl A B) ≡ refl
      pf = refl

{- WAS:
refl !=
fromIso (foo.pf.iso-f refl A B) (foo.pf.iso-g refl A B)
(foo.pf.iso-η refl A B) (foo.pf.iso-ε refl A B)
(foo.pf.iso-τ refl A B)
of type ((x : A γ) → B γ x) ≡ ((x : A γ) → B γ x)
when checking that the expression pf has type
foo.pf refl A B ≡ refl
-}
