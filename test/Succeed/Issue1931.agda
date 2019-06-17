{-# OPTIONS --rewriting --confluence-check --allow-unsolved-metas #-}

postulate
  C  : Set

  D  : Set → Set
  d₁ : (A : Set) → D A
  d₂ : (A : Set) → (C → D A) → D A

  E  : (A : Set) → A → A → Set
  e₁ : (A : Set) (j₁ j₂ : C → D A) →
       ((c : C) → E (D A) (j₁ c) (j₂ c)) →
       (y : D A) →
       E (D A) (d₂ A j₁) y

  f  : (A B : Set) → D A → D B
  f₁ : (A B : Set) → E (D B) (f A B (d₁ A)) (d₁ B)
  f₂ : (A B : Set) (j : C → D A) →
       E (D B) (f A B (d₂ A j)) (d₂ B (λ c → f A B (j c)))

  g  : (A : Set) (Q : D A → Set) →
       Q (d₁ A) →
       ((j : C → D A) → ((c : C) → Q (j c)) → Q (d₂ A j)) →
       (c : D A) → Q c

{-# BUILTIN REWRITE E #-}
{-# REWRITE f₁        #-}
{-# REWRITE f₂        #-}

h : (A B : Set)
    (i : D A → D B) →
    E (D B) (d₁ B) (i (d₁ A)) →
    (d : D A) → E (D B) (f A B d) (i d)
h A B i e₂ = g
  A
  (λ (d : D A) → E (D B) {!f A B d!} (i d))
  e₂
  (λ j q → e₁ B (λ c → f A B (j c)) (λ c → i (j c)) q (i (d₂ A j)))
