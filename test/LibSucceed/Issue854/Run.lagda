\subsection{Meta-theoretic constructions related to the running of
            effects}
\label{run}

In this section we develop the machinery needed to run (parts of)
effects. This was done in my first year report for containers.

\AgdaHide{
\begin{code}
{-# OPTIONS --sized-types #-}

module Issue854.Run where

open import Level using (lower)
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product as Prod
open import Data.List.Relation.Unary.Any
open import Data.Container as Cont hiding (_∈_)
    renaming (⟦_⟧ to ⟦_⟧^C; μ to μ^C; _⇒_ to _⇒^C_)
open import Data.Container.Combinator using () renaming (_⊎_ to _⊎^C_)
open import Data.Container.FreeMonad
    renaming (_⋆_ to _⋆^C_; _⋆C_ to _⋆^CC_)
open import Data.W
open import Category.Monad

open import Issue854.Types using (Sig)
open import Issue854.TypesSemantics using (⌊_⌋^Sig)
open import Data.List.Membership.Propositional
\end{code}
}

\begin{code}
rec : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c} →
        (Σ[ x ∈ A ] (B x → W (A ▷ B) × C) → C) → W (A ▷ B) → C
rec f (sup (s , k)) = f (s , (λ p → (k p , rec f (k p))))

_⋆^S_ : Sig → Set → Set
Σ ⋆^S X = μ^C (⌊ Σ ⌋^Sig ⋆^CC X)

ALG : Container _ _ → Set → Set
ALG Σ X = ⟦ Σ ⟧^C X → X

PALG : Container _ _ → Set → Set
PALG Σ X = ⟦ Σ ⟧^C (μ^C Σ × X) → X

HOMO : Container _ _ → Set → Set → Container _ _ → Set → Set
HOMO Σ X I Σ′ Y = PALG (Σ ⋆^CC X) (I → Σ′ ⋆^C Y)

HOMO′ : Container _ _ → Container _ _ → Set → Set → Container _ _ → Set → Set
HOMO′ Σ Σ′ X I Σ″ Y = ⟦ Σ ⋆^CC X ⟧^C
    ((Σ′ ⋆^C X) × (I → Σ″ ⋆^C Y)) → (I → Σ″ ⋆^C Y)

PHOMO : Container _ _ → Set → Set → Container _ _ → Set → Set
PHOMO Σ X I Σ′ Y = ⟦ Σ ⋆^CC X ⟧^C
    (((Σ ⊎^C Σ′) ⋆^C X) × (I → Σ′ ⋆^C Y)) → I → Σ′ ⋆^C Y

PHOMO′ : Container _ _ → Container _ _ → Set → Set → Container _ _ → Set → Set
PHOMO′ Σ Σ′ X I Σ″ Y = ⟦ Σ ⋆^CC X ⟧^C
    (((Σ′ ⊎^C Σ″) ⋆^C X) × (I → Σ″ ⋆^C Y)) → I → Σ″ ⋆^C Y

⟪_⟫^⊆ : ∀ {Σ Σ′ Σ″ X} → Σ ⇒^C Σ″ → HOMO′ Σ Σ′ X ⊤ Σ″ X
⟪_⟫^⊆ m (inj₁ x , k)  _ = M.return x
  where
  module M = RawMonad rawMonad
⟪ m ⟫^⊆ (inj₂ s , k)  _ =  let (s′ , k′) = ⟪ m ⟫ (s , k)
                           in  inn (s′ , λ p′ → proj₂ (k′ p′) tt)

embed : ∀ {Σ Σ′ X} → Σ ⇒^C Σ′ → Σ ⋆^C X → Σ′ ⋆^C X
embed {X = X} f m = rec ⟪ f ⟫^⊆ m tt

inlMorph : ∀ {ℓ}{C C′ : Container ℓ ℓ} → C ⇒^C (C ⊎^C C′)
inlMorph = record
  { shape    = inj₁
  ; position = λ p → p
  }

inl : ∀ {Σ Σ′ X} → Σ ⋆^C X → (Σ ⊎^C Σ′) ⋆^C X
inl = embed inlMorph

squeeze : ∀ {Σ Σ′ X} → ((Σ ⊎^C Σ′) ⊎^C Σ′) ⋆^C X → (Σ ⊎^C Σ′) ⋆^C X
squeeze = embed m
  where
  m = record
    { shape    = [ id , inj₂ ]′
    ; position = λ { {inj₁ x} → id ; {inj₂ x} → id }
    }

lift : ∀ {Σ Σ′ X Y I} → PHOMO Σ X I Σ′ Y → PHOMO (Σ ⊎^C Σ′) X I Σ′ Y
lift φ (inj₁ x , _)          i = φ (inj₁ x , ⊥-elim ∘ lower) i
lift φ (inj₂ (inj₁ s) , k)   i = φ (inj₂ s , λ p →
                                     let (w , ih) = k p in squeeze w , ih) i
lift φ (inj₂ (inj₂ s′) , k′) i = inn (s′ , λ p′ → proj₂ (k′ p′) i)

weaken : ∀ {Σ Σ′ Σ″ Σ‴ X Y I} → HOMO Σ′ X I Σ″ Y → Σ ⇒^C Σ′ → Σ″ ⇒^C Σ‴ →
           HOMO Σ X I Σ‴ Y
weaken {Σ}{Σ′}{Σ″}{Σ‴}{X}{Y} φ f g (s , k) i = w‴
  where
  w : Σ ⋆^C X
  w = sup (s , proj₁ ∘ k)

  w′ : Σ′ ⋆^C X
  w′ = embed f w

  w″ : Σ″ ⋆^C Y
  w″ = rec φ w′ i

  w‴ : Σ‴ ⋆^C Y
  w‴ = embed g w″

⌈_⌉^HOMO : ∀ {Σ Σ′ X Y I} → PHOMO Σ X I Σ′ Y → HOMO Σ X I Σ′ Y
⌈ φ ⌉^HOMO (inj₁ x , _)  = φ (inj₁ x , ⊥-elim ∘ Level.lower)
⌈ φ ⌉^HOMO (inj₂ s , k)  = φ (inj₂ s , Prod.map inl id ∘ k)

RUN : ∀ {Σ Σ′ Σ″ Σ‴ X Y I} → PHOMO Σ′ X I Σ″ Y → Σ ⇒^C (Σ′ ⊎^C Σ″) → Σ″ ⇒^C Σ‴ →
        Σ ⋆^C X → I → Σ‴ ⋆^C Y
RUN φ p q = rec (weaken (⌈ lift φ ⌉^HOMO) p q)
\end{code}
