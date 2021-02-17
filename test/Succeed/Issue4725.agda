{-# OPTIONS --cubical #-}

open import Agda.Builtin.Sigma

mutual

  data D : Set where
    d : S → D

  S : Set
  S = Σ D λ x → R x

  fst′ : S → D
  fst′ s = fst s

  data R : D → Set where
    r : ∀ x → R (fst′ x) → R (d x)

module _
  (P : D → Set)
  (Q : ∀ x → P x → R x → Set)
  (p : ∀ s (p : P (fst s)) → Q (fst s) p (snd s) → P (d s))
  (q : ∀ s rs (ps : P (fst s)) (qs : Q (fst s) ps (snd s)) →
       Q (fst s) ps rs → Q (d s) (p s ps qs) (r s rs))
  where

  mutual

    f : (x : D) → P x
    f (d (x , r₁)) = p (x , r₁) (f x) (g x r₁)

    g : (x : D) (x⊑y : R x) → Q x (f x) x⊑y
    g (d (x , r₁)) (r .(x , r₁) r₂) =
      q (x , r₁) r₂ (f x) (g x r₁) (g _ r₂)
