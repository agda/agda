{-# OPTIONS --allow-unsolved-metas #-}

-- Andreas, 2014-12-06
-- Reported by sanzhiyan, Dec 4 2014

open import Data.Vec
open import Data.Fin
open import Data.Nat renaming (_+_ to _+N_)
open import Data.Nat.Solver
open import Relation.Binary.PropositionalEquality hiding ([_])
open +-*-Solver using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

data prop : Set where
  F T   : prop
  _∧_ _∨_ : prop → prop → prop

infixl 4 _∧_ _∨_

Γ : (n : ℕ) → Set
Γ n = Vec prop n

infix 1 _⊢_

data _⊢_ : ∀ {n} → Γ n → prop → Set  where
  hyp     : ∀ {n}(C : Γ n)(v : Fin n) → C ⊢ (lookup C v)
  andI    : ∀ {n}{C : Γ n}{p p' : prop} → C ⊢ p → C ⊢ p' → C ⊢ p ∧ p'
  andEL   : ∀ {n}{C : Γ n}{p p' : prop} → C ⊢ p ∧ p' → C ⊢ p
  andER   : ∀ {n}{C : Γ n}{p p' : prop} → C ⊢ p ∧ p' → C ⊢ p'
  orIL    : ∀ {n}{C : Γ n}{p : prop}(p' : prop) → C ⊢ p → C ⊢ p ∨ p'
  orIR    : ∀ {n}{C : Γ n}{p' : prop}(p : prop) → C ⊢ p' → C ⊢ p ∨ p'
  orE     : ∀ {n}{C : Γ n}{p p' c : prop} → C ⊢ p ∨ p' → p ∷ C ⊢ c → p' ∷ C ⊢ c →  C ⊢ c

-- WAS:
-- The first two _ could not be solved before today's (2014-12-06) improvement of pruning.
-- Except for variables, they were applied to a huge neutral proof term coming from the ring solver.
-- Agda could not prune before the improved neutrality check implemented by Andrea(s) 2014-12-05/06.
--
-- As a consequence, Agda would often reattempt solving, each time doing the expensive
-- occurs check.  This would extremely slow down Agda.

weakening : ∀ {n m p p'}(C : Γ n)(C' : Γ m) → C ++ C' ⊢ p → C ++ [ p' ] ++ C' ⊢ p
weakening {n} {m} {p' = p'} C C' (hyp .(C ++ C') v) = subst (λ R → C ++ (_ ∷ C') ⊢ R) {!!}
          (hyp (C ++ (_ ∷ C')) (subst (λ x → Fin x) proof (inject₁ v))) where
        proof : suc (n +N m) ≡ n +N suc m
        proof = (solve 2 (λ n₁ m₁ → con 1 :+ (n₁ :+ m₁) := n₁ :+ (con 1 :+ m₁)) refl n m)
weakening C C' (andI prf prf') = andI (weakening C C' prf) (weakening C C' prf')
weakening C C' (andEL prf) = andEL (weakening C C' prf)
weakening C C' (andER prf) = andER (weakening C C' prf)
weakening C C' (orIL p'' prf) = orIL p'' (weakening C C' prf)
weakening C C' (orIR p prf) = orIR p (weakening C C' prf)
weakening C C' (orE prf prf₁ prf₂) = orE (weakening C C' prf) (weakening (_ ∷ C) C' prf₁) (weakening (_ ∷ C) C' prf₂)

-- Should check fast now and report the ? as unsolved meta.
