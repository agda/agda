%include agda.fmt

\subsection{The semantics of types}
\label{types-semantics}

\AgdaHide{
\begin{code}
{-# OPTIONS --sized-types #-}

module Issue854.TypesSemantics where

import Level
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.Container hiding (_∈_) renaming (μ to μ^C; ⟦_⟧ to ⟦_⟧^C; _▷_ to _◃_)
open import Data.Container.Combinator using () renaming (_×_ to _×^C_)
open import Data.Container.FreeMonad as FM
    hiding (_⋆_) renaming (_⋆C_ to _⋆^CC_)
open import Category.Monad
open import Relation.Binary.PropositionalEquality

open import Data.List.Membership.Propositional
open import Issue854.Types
open import Issue854.Context
open import Issue854.EilenbergMooreAlgebra
\end{code}
}

\begin{code}
mutual
  ⟦_⟧^VType : VType → Set
  ⟦ ⁅ C ⁆  ⟧^VType = Carrier ⟦ C ⟧^CType
  ⟦ 𝟙      ⟧^VType = ⊤
  ⟦ U ⊗ V  ⟧^VType = ⟦ U ⟧^VType × ⟦ V ⟧^VType
  ⟦ 𝟘      ⟧^VType = ⊥
  ⟦ U ⊕ V  ⟧^VType = ⟦ U ⟧^VType ⊎ ⟦ V ⟧^VType
  ⟦ μ Δ    ⟧^VType = μ^C ⌊ Δ ⌋^Sig

  ⌊_⌋^Sig : Sig → Container _ _
  ⌊ Σ ⌋^Sig = Sh Σ ◃ Pos Σ

  Sh : Sig → Set
  Sh []             = ⊥
  Sh ((P , _) ∷ Σ)  = ⟦ P ⟧^VType ⊎ Sh Σ

  Pos : (Σ : Sig) → Sh Σ → Set
  Pos []             ()
  Pos ((_ , A) ∷ Σ)  (inj₁ p) = ⟦ A ⟧^VType
  Pos ((_ , A) ∷ Σ)  (inj₂ s) = Pos Σ s

  ∣_∣^Sig : CType → Container _ _
  ∣ Σ ⋆ V  ∣^Sig = ⌊ Σ ⌋^Sig
  ∣ V ⇒ C  ∣^Sig = ∣ C ∣^Sig
  ∣ ⊤′     ∣^Sig = ⌊ [] ⌋^Sig
  ∣ B & C  ∣^Sig = ∣ B ∣^Sig ×^C ∣ C ∣^Sig

  ⟦_⟧^CType : (C : CType) → ∣ C ∣^Sig -Alg
  ⟦ Σ ⋆ V  ⟧^CType = ⋆-alg ⟦ V ⟧^VType
  ⟦ V ⇒ C  ⟧^CType = ⟦ V ⟧^VType ⇒-alg ⟦ C ⟧^CType
  ⟦ ⊤′     ⟧^CType = ⋆-alg ⊤
  ⟦ B & C  ⟧^CType = ⟦ B ⟧^CType ⊙-alg ⟦ C ⟧^CType

-- What if we wanted to add cofree comonads/free cims? The following is
-- a bit complicated, but seems to suggest that it should be possible?
mutual
  data ∣_∣^Alg : CType → Set where
    alg : ∀ {C} → ∣ C ∣^Alg

  ∣_∣^Alg′ : (C : CType) → ∣ C ∣^Alg
  ∣ C ∣^Alg′ = alg

  El^Alg : ∀ {C} → ∣ C ∣^Alg → Set₁
  El^Alg {C} alg = ∣ C ∣^Sig -Alg

  ⟦_⟧^VType′ : VType → Set
  ⟦ ⁅ C ⁆  ⟧^VType′ = Carrier′ {C}{∣ C ∣^Alg′} (⟦ C ⟧^CType′ {A = ∣ C ∣^Alg′ })
  ⟦ 𝟙      ⟧^VType′ = ⊤
  ⟦ U ⊗ V  ⟧^VType′ = ⟦ U ⟧^VType × ⟦ V ⟧^VType
  ⟦ 𝟘      ⟧^VType′ = ⊥
  ⟦ U ⊕ V  ⟧^VType′ = ⟦ U ⟧^VType ⊎ ⟦ V ⟧^VType
  ⟦ μ Δ    ⟧^VType′ = μ^C ⌊ Δ ⌋^Sig

  Carrier′ : ∀ {C} {A : ∣ C ∣^Alg} → El^Alg A → Set
  Carrier′ {C} {alg} A = Carrier A

  ⟦_⟧^CType′ : (C : CType) → {A : ∣ C ∣^Alg} → El^Alg A
  ⟦ Σ ⋆ V  ⟧^CType′ {alg} = ⋆-alg ⟦ V ⟧^VType
  ⟦ V ⇒ C  ⟧^CType′ {alg} = ⟦ V ⟧^VType ⇒-alg ⟦ C ⟧^CType
  ⟦ ⊤′     ⟧^CType′ {alg} = ⋆-alg ⊤
  ⟦ B & C  ⟧^CType′ {alg} = ⟦ B ⟧^CType ⊙-alg ⟦ C ⟧^CType


⟦_⟧^Ctx : Ctx → Set
⟦ []     ⟧^Ctx = ⊤
⟦ Γ ▻ V  ⟧^Ctx = ⟦ Γ ⟧^Ctx × ⟦ V ⟧^VType

⟦_⟧^CTypes : List CType → Set
⟦ []      ⟧^CTypes = ⊤
⟦ C ∷ Cs  ⟧^CTypes = Carrier ⟦ C ⟧^CType × ⟦ Cs ⟧^CTypes

⟦_⟧^Sig : Sig → (Set → Set)
⟦ Σ ⟧^Sig = ⟦ ⌊ Σ ⌋^Sig ⟧^C

sh : ∀ {Σ P A} → (P , A) ∈ Σ → ⟦ P ⟧^VType → Sh Σ
sh (here refl)  p = inj₁ p
sh (there m)    p = inj₂ (sh m p)

ar : ∀ {Σ P A}(m : (P , A) ∈ Σ)(p : ⟦ P ⟧^VType) → Pos Σ (sh m p) →
       ⟦ A ⟧^VType
ar (here refl)  _  a = a
ar (there m)    p  a = ar m p a
\end{code}
