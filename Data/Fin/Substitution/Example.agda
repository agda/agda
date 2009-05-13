------------------------------------------------------------------------
-- An example of how Data.Fin.Substitution can be used: a definition
-- of substitution for the untyped λ-calculus, along with some lemmas
------------------------------------------------------------------------

module Data.Fin.Substitution.Example where

open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat
open import Data.Fin using (Fin)
open import Data.Vec
import Data.Function as Fun
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning
open import Data.Star using (Star; ε; _◅_; _▻_)

-- A representation of the untyped λ-calculus. Uses de Bruijn
-- notation.

infixl 9 _·_

data Tm (n : ℕ) : Set where
  var : (x : Fin n) → Tm n
  ƛ   : (t : Tm (suc n)) → Tm n
  _·_ : (t₁ t₂ : Tm n) → Tm n

-- Some Tm-related substitution functions.

record TmSubst (T : ℕ → Set) : Set where
  field
    simple : Simple T
    term   : ∀ {n} → T n → Tm n  -- Takes Ts to terms.

  open Simple simple public hiding (var; weaken)

  -- Application of a substitution to a term.

  infixl 8 _/_

  _/_ : ∀ {m n} → Tm m → Sub T m n → Tm n
  var x   / ρ = term (lookup x ρ)
  ƛ t     / ρ = ƛ (t / ρ ↑)
  t₁ · t₂ / ρ = (t₁ / ρ) · (t₂ / ρ)

  application : Application Tm T
  application = record { _/_ = _/_ }

  open Application application public hiding (_/_)

  -- Weakening of terms.

  weaken : ∀ {n} → Tm n → Tm (suc n)
  weaken t = t / wk

  -- Some lemmas which are specific to the definition of _/_ given
  -- above.

  ƛ-/✶-↑✶ : ∀ k {m n t} (ρs : Subs T m n) →
            ƛ t /✶ ρs ↑✶ k ≡ ƛ (t /✶ ρs ↑✶ suc k)
  ƛ-/✶-↑✶ k ε        = refl
  ƛ-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (ƛ-/✶-↑✶ k ρs) refl

  ·-/✶-↑✶ : ∀ k {m n t₁ t₂} (ρs : Subs T m n) →
            t₁ · t₂ /✶ ρs ↑✶ k ≡ (t₁ /✶ ρs ↑✶ k) · (t₂ /✶ ρs ↑✶ k)
  ·-/✶-↑✶ k ε        = refl
  ·-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (·-/✶-↑✶ k ρs) refl

-- Another lemma.

module TmSubstLemma
         {T₁ T₂ : ℕ → Set}
         (tmSubst₁ : TmSubst T₁)
         (tmSubst₂ : TmSubst T₂)
         where

  private
    open module T₁ = TmSubst tmSubst₁ using ()
      renaming (_/✶_ to _/✶₁_; _↑✶_ to _↑✶₁_)
    open module T₂ = TmSubst tmSubst₂ using ()
      renaming (_/✶_ to _/✶₂_; _↑✶_ to _↑✶₂_)

  /✶-↑✶ : ∀ {m n} (ρs₁ : Subs T₁ m n) (ρs₂ : Subs T₂ m n) →
          (∀ k {x} → var x /✶₁ ρs₁ ↑✶₁ k ≡ var x /✶₂ ρs₂ ↑✶₂ k) →
          ∀ k {t} → t /✶₁ ρs₁ ↑✶₁ k ≡ t /✶₂ ρs₂ ↑✶₂ k
  /✶-↑✶ ρs₁ ρs₂ hyp k {var x} = hyp k
  /✶-↑✶ ρs₁ ρs₂ hyp k {ƛ t}   = begin
    ƛ t /✶₁ ρs₁ ↑✶₁ k        ≡⟨ T₁.ƛ-/✶-↑✶ k ρs₁ ⟩
    ƛ (t /✶₁ ρs₁ ↑✶₁ suc k)  ≡⟨ cong ƛ (/✶-↑✶ ρs₁ ρs₂ hyp (suc k)) ⟩
    ƛ (t /✶₂ ρs₂ ↑✶₂ suc k)  ≡⟨ sym (T₂.ƛ-/✶-↑✶ k ρs₂) ⟩
    ƛ t /✶₂ ρs₂ ↑✶₂ k        ∎
  /✶-↑✶ ρs₁ ρs₂ hyp k {t₁ · t₂} = begin
    t₁ · t₂ /✶₁ ρs₁ ↑✶₁ k                    ≡⟨ T₁.·-/✶-↑✶ k ρs₁ ⟩
    (t₁ /✶₁ ρs₁ ↑✶₁ k) · (t₂ /✶₁ ρs₁ ↑✶₁ k)  ≡⟨ cong₂ _·_ (/✶-↑✶ ρs₁ ρs₂ hyp k)
                                                          (/✶-↑✶ ρs₁ ρs₂ hyp k) ⟩
    (t₁ /✶₂ ρs₂ ↑✶₂ k) · (t₂ /✶₂ ρs₂ ↑✶₂ k)  ≡⟨ sym (T₂.·-/✶-↑✶ k ρs₂) ⟩
    t₁ · t₂ /✶₂ ρs₂ ↑✶₂ k                    ∎

-- Variable substitutions (for terms).

module VarTmSubst where

  tmSubst : TmSubst Fin
  tmSubst = record { simple = VarSubst.simple; term = var }

  open TmSubst tmSubst public

-- Term substitutions.

module TmTmSubst where

  tmSubst : TmSubst Tm
  tmSubst = record
    { simple = record
      { var    = var
      ; weaken = VarTmSubst.weaken
      }
    ; term = Fun.id
    }

  open TmSubst tmSubst

  lemmas₃ : Lemmas₃ Tm
  lemmas₃ = record
    { lemmas₂ = record
      { lemmas₁ = record
        { lemmas₀ = record
          { simple = simple
          }
        ; weaken-var = cong var (VarLemmas.lookup-wk _)
        }
      ; application = application
      ; var-/       = refl
      }
    ; /✶-↑✶ = TmSubstLemma./✶-↑✶ tmSubst tmSubst
    }

  lemmas₄ : Lemmas₄ Tm
  lemmas₄ = record
    { lemmas₃ = lemmas₃
    ; /-wk    = λ {_ t} →
        TmSubstLemma./✶-↑✶ tmSubst VarTmSubst.tmSubst
          (ε ▻ wk) (ε ▻ VarSubst.wk)
          (VarLemmas.var-/-wk-↑⋆ (Lemmas₃.lemmas₂ lemmas₃))
          zero {t}
    }

  open Lemmas₄ lemmas₄ public hiding (lemmas₃; subst)
