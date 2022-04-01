%include agda.fmt

\subsection{Eilenberg-Moore algebras}
\label{em-algs}

\AgdaHide{
\begin{code}
{-# OPTIONS --sized-types #-}

module Issue854.EilenbergMooreAlgebra where

open import Function
open import Data.Sum
open import Data.Product as Prod
open import Data.Container renaming (⟦_⟧ to ⟦_⟧^C)
open import Data.Container.Combinator using ()
    renaming (_×_ to _×^C_)
open import Data.Container.FreeMonad
    renaming (_⋆_ to _⋆^C_; _⋆C_ to _⋆^CC_)
open import Data.W
open import Effect.Monad
\end{code}
}

\begin{code}
iter : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c} →
         (Σ[ x ∈ A ] (B x → C) → C) → W (A ▷ B) → C
iter g (sup (x , f)) = g (x , λ b → iter g (f b))

module T-algebra
  (T : Set → Set)
  (M : RawMonad T)
  where

  open RawMonad M

  -- Eilenberg-Moore algebra for a monad T on Set
  record T-Alg : Set₁ where
    constructor alg
    field
      Carrier    : Set
      structure  : T Carrier → Carrier

  open T-Alg public

  -- Generalised bind operator.
  bind : ∀ {X}(A : T-Alg) → T X → (X → Carrier A) → Carrier A
  bind A tx f = structure A (f <$> tx)

  -- Free algebra
  ⋆-alg : Set → T-Alg
  ⋆-alg X = alg (T X) join

  -- Exponential algebras
  _⇒-alg_ : Set → T-Alg → T-Alg
  X ⇒-alg alg C φ = alg (X → C) (λ a x →  φ (a ⊛ return x))

  -- Product algebras
  _×-alg_ : T-Alg → T-Alg → T-Alg
  alg C φ ×-alg alg C′ φ′ = alg (C × C′)
      < φ ∘ _<$>_ proj₁ , φ′ ∘ _<$>_ proj₂ >

-- Eilenberg-Moore algebras for free monads.

module _ {Σ : Container _ _} where

  open T-algebra (_⋆^C_ Σ) rawMonad public

_-Alg : Container _ _ → Set₁
Σ -Alg = T-Alg {Σ}

-- A more general product algebra.
_⊙-alg_ : ∀ {Σ Σ′} → Σ -Alg → Σ′ -Alg → (Σ ×^C Σ′) -Alg
alg C φ ⊙-alg alg C′ φ′ = alg (C × C′) (Prod.map φ φ′ ∘ split-⋆×)
  where
  split-⋆× : ∀ {Σ Σ′}{X Y : Set} → (Σ ×^C Σ′) ⋆^C (X × Y) →
             (Σ ⋆^C X) × (Σ′ ⋆^C Y)
  split-⋆× {Σ}{Σ′}{X}{Y} = iter α
    where
    α : let C = (Σ ⋆^C X) × (Σ′ ⋆^C Y) in
        ⟦ (Σ ×^C Σ′) ⋆^CC X × Y ⟧^C C → C
    α (inj₁ (x , y)  , _)  =  RawMonad.return rawMonad x ,
                              RawMonad.return rawMonad y
    α (inj₂ (s , s′) , k)  =  inn (s  , proj₁ ∘ k ∘ inj₁) ,
                              inn (s′ , proj₂ ∘ k ∘ inj₂)
\end{code}

\begin{code}
-- Using container exponents can we construct:

-- _⇒′-alg_ : Σ -Alg → Σ′ -Alg → Σ ⟶ Σ′ -Alg?

-- Which could be used to denote the function space between two
-- computation types?!
\end{code}
