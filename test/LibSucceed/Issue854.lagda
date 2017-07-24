% Andreas, Bug filed by Stevan Andjelkovic, June 2013

\subsection{Examples}
\label{examples}

\AgdaHide{
\begin{code}
module Issue854 where

open import Function
open import Data.Unit
open import Data.Product
open import Data.List
open import Data.List.Any
open import Data.Container.FreeMonad using (rawMonad)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.List.Pointwise hiding (refl)
open import Category.Monad

open import Data.List.Any.Membership.Propositional
open import Issue854.Types
open import Issue854.Context
open import Issue854.WellTyped
open import Issue854.WellTypedSemantics
\end{code}
}

\begin{code}
′N : Sig
′N = (𝟙 , 𝟘) ∷ (𝟙 , 𝟙) ∷ []

N = μ ′N

ze : ∀ {Γ} → Γ ⊢^v _ ∶ N
ze = con (here refl) ⟨⟩ (𝟘-elim (var zero))

pattern su n = con (there (here refl)) ⟨⟩ n

#0 #1 : ∀ {Γ} → Γ ⊢^v _ ∶ N

#0 = ze
#1 = su #0

State : VType → Sig
State S = (𝟙 , S) ∷ (S , 𝟙) ∷ []

-- XXX: get : {m : True (𝟙 , S) ∈? Σ)} → Σ ⋆ S?

state^suc : ∀ {Γ} → Γ ⊢^c _ ∶ State N ⋆ 𝟙
state^suc {Γ} = _to_ (op get · ⟨⟩) (op put · su′) id id
  where
  get = here refl
  put = there (here refl)

  su′ : Γ ▻ N ⊢^v _ ∶ N
  su′ = con (there (here refl)) ⟨⟩ (var (suc zero))

state^Homo : ∀ {Γ Σ S X} → Γ ⊢^cs _ ∶ PHomo (State S) X S Σ (X ⊗ S)
state^Homo =
  ƛ ƛ ƛ (((π₂ (force (var (suc zero)) · var zero)) · var zero)) ∷
  ƛ ƛ ƛ ((π₂ (force (var (suc zero)) · ⟨⟩)) · var (suc (suc zero))) ∷
  ƛ ƛ return (var (suc zero) , var zero) ∷ []

private
  -- XXX: Move to std-lib?
  inl-++ : ∀ {A : Set}{xs ys : List A} → xs ⊆ (xs ++ ys)
  inl-++ {xs = []}      ()
  inl-++ {xs = x ∷ xs}  (here refl)  = here refl
  inl-++ {xs = x ∷ xs}  (there p)    = there (inl-++ p)

  inr-++ : ∀ {A : Set}{xs ys : List A} → ys ⊆ (xs ++ ys)
  inr-++ {xs = []}      p = p
  inr-++ {xs = x ∷ xs}  p = there (inr-++ {xs = xs} p)

ex-state : [] ⊢^c _ ∶ [] ⋆ (𝟙 ⊗ N)
ex-state = run {Σ′ = State N}{[]} state^Homo state^suc inl-++ id · #0

test-state : ⟦ ex-state ⟧^c tt ≡ ⟦ return (⟨⟩ , #1) ⟧^c tt
test-state = refl
\end{code}
