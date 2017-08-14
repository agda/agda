------------------------------------------------------------------------
-- The Agda standard library
--
-- A generalisation of the arithmetic operations
------------------------------------------------------------------------

module Data.Nat.GeneralisedArithmetic where

open import Data.Nat
open import Data.Nat.Properties
open import Function using (_∘′_; _∘_; id)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module _ {a} {A : Set a} where

  fold : A → (A → A) → ℕ → A
  fold z s zero    = z
  fold z s (suc n) = s (fold z s n)

  add : (0# : A) (1+ : A → A) → ℕ → A → A
  add 0# 1+ n z = fold z 1+ n

  mul : (0# : A) (1+ : A → A) → (+ : A → A → A) → (ℕ → A → A)
  mul 0# 1+ _+_ n x = fold 0# (λ s → x + s) n

-- Properties

module _ {a} {A : Set a} where

  fold-+ : ∀ {s : A → A} {z : A} →
           ∀ m {n} → fold z s (m + n) ≡ fold (fold z s n) s m
  fold-+ zero    = refl
  fold-+ {s = s} (suc m) = cong s (fold-+ m)

  fold-k : ∀ {s : A → A} {z : A} {k} m →
           fold k (s ∘′_) m z ≡ fold (k z) s m
  fold-k zero    = refl
  fold-k {s = s} (suc m) = cong s (fold-k m)

  fold-* : ∀ {s : A → A} {z : A} m {n} →
           fold z s (m * n) ≡ fold z (fold id (s ∘_) n) m
  fold-*  zero        = refl
  fold-* {s = s} {z} (suc m) {n} = let +n = fold id (s ∘′_) n in begin
    fold z s (n + m * n)        ≡⟨ fold-+ n ⟩
    fold (fold z s (m * n)) s n ≡⟨ cong (λ z → fold z s n) (fold-* m) ⟩
    fold (fold z +n m) s n      ≡⟨ sym (fold-k n) ⟩
    fold z +n (suc m)           ∎

  fold-pull : ∀ {s : A → A} {z : A} (g : A → A → A) (p : A)
              (eqz : g z p ≡ p)
              (eqs : ∀ l → s (g l p) ≡ g (s l) p) →
              ∀ m → fold p s m ≡ g (fold z s m) p
  fold-pull _ _ eqz _ zero    = sym eqz
  fold-pull {s = s} {z} g p eqz eqs (suc m) = begin
    s (fold p s m)       ≡⟨ cong s (fold-pull g p eqz eqs m) ⟩
    s (g (fold z s m) p) ≡⟨ eqs (fold z s m) ⟩
    g (s (fold z s m)) p ∎

id-is-fold : ∀ m → fold zero suc m ≡ m
id-is-fold zero    = refl
id-is-fold (suc m) = cong suc (id-is-fold m)

+-is-fold : ∀ m {n} → fold n suc m ≡ m + n
+-is-fold zero    = refl
+-is-fold (suc m) = cong suc (+-is-fold m)

*-is-fold : ∀ m {n} → fold zero (n +_) m ≡ m * n
*-is-fold zero        = refl
*-is-fold (suc m) {n} = cong (n +_) (*-is-fold m)

^-is-fold : ∀ {m} n → fold 1 (m *_) n ≡ m ^ n
^-is-fold     zero    = refl
^-is-fold {m} (suc n) = cong (m *_) (^-is-fold n)

*+-is-fold : ∀ m n {p} → fold p (n +_) m ≡ m * n + p
*+-is-fold m n {p} = begin
  fold p (n +_) m     ≡⟨ fold-pull _+_ p refl
                         (λ l → sym (+-assoc n l p)) m ⟩
  fold 0 (n +_) m + p ≡⟨ cong (_+ p) (*-is-fold m) ⟩
  m * n + p           ∎

^*-is-fold : ∀ m n {p} → fold p (m *_) n ≡ m ^ n * p
^*-is-fold m n {p} = begin
  fold p (m *_) n     ≡⟨ fold-pull _*_ p (*-identityˡ p)
                         (λ l → sym (*-assoc m l p)) n ⟩
  fold 1 (m *_) n * p ≡⟨ cong (_* p) (^-is-fold n) ⟩
  m ^ n * p           ∎
