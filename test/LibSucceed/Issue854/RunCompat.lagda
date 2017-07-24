\subsection{Compatibility layer between containers and signatures}
\label{run-compat}

In section \ref{run} we developed a library for working with effects in
free monads of containers. Since signatures (list of pairs of types) are
used in our langauge rather than containers directly, we will now give a
compatibility layer between containers and signatures.

\AgdaHide{
\begin{code}
module Issue854.RunCompat where

open import Level
open import Function
open import Function.Equivalence using (_⇔_)
open import Data.Empty
open import Data.Sum
open import Data.Product as Prod
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Any
open import Data.Container as Cont hiding (_∈_)
    renaming (⟦_⟧ to ⟦_⟧^C; μ to μ^C; _⇒_ to _⇒^C_)
open import Data.Container.Combinator using (module Sum) renaming (_⊎_ to _⊎^C_)
open import Data.Container.FreeMonad
    renaming (_⋆_ to _⋆^C_; _⋆C_ to _⋆^CC_)
open import Data.W
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE hiding ([_])

open import Data.List.Any.Membership.Propositional
open import Issue854.TypesSemantics using (Sh; Pos; ⌊_⌋^Sig; sh; ar)
open import Issue854.Run using (_⋆^S_; embed)
\end{code}
}

\begin{code}
⊆→⇒ : ∀ {Σ Σ′} → Σ ⊆ Σ′ → ⌊ Σ ⌋^Sig ⇒^C ⌊ Σ′ ⌋^Sig
⊆→⇒ σ = record
  { shape     = shape′ σ
  ; position  = λ {s} → pos σ s
  }
  where
  shape′ : ∀ {Σ Σ′} → Σ ⊆ Σ′ → Sh Σ → Sh Σ′
  shape′ {[]}     _ ()
  shape′ {_ ∷ _}  σ (inj₁ p)  = sh (σ (here refl)) p
  shape′ {_ ∷ _}  σ (inj₂ s)  = shape′ (σ ∘ there) s

  pos : ∀ {Σ Σ′}(σ : Σ ⊆ Σ′) s → Pos Σ′ (shape′ σ s) → Pos Σ s
  pos {[]}     σ ()          _
  pos {_ ∷ _}  σ (inj₁ par)  p  = ar (σ (here refl)) par p
  pos {_ ∷ _}  σ (inj₂ s)    p  = pos (σ ∘ there) s p
\end{code}

\begin{code}
⇒++→⇒⊎ : ∀ {Σ Σ′ Σ″} → ⌊ Σ ⌋^Sig ⇒^C ⌊ Σ′ ++ Σ″ ⌋^Sig →
           ⌊ Σ ⌋^Sig ⇒^C (⌊ Σ′ ⌋^Sig ⊎^C ⌊ Σ″ ⌋^Sig)
⇒++→⇒⊎ m = m′ Morphism.∘ m
  where
  m′ : ∀ {Σ Σ′} → ⌊ Σ ++ Σ′ ⌋^Sig ⇒^C (⌊ Σ ⌋^Sig ⊎^C ⌊ Σ′ ⌋^Sig)
  m′ {Σ} = record
    { shape     = shape′
    ; position  = λ {s} → pos {Σ} s
    }
    where
    shape′ : ∀ {Σ Σ′} → Sh (Σ ++ Σ′) → Sh Σ ⊎ Sh Σ′
    shape′ {[]}    s′          = inj₂ s′
    shape′ {_ ∷ _} (inj₁ p)    = inj₁ (inj₁ p)
    shape′ {_ ∷ Σ} (inj₂ ss′)  = [ inj₁ ∘ inj₂ , inj₂ ]′ (shape′ {Σ} ss′)

    pos : ∀ {Σ Σ′} s → Position (⌊ Σ ⌋^Sig ⊎^C ⌊ Σ′ ⌋^Sig) (shape′ s) →
            Position ⌊ Σ ++ Σ′ ⌋^Sig s
    pos {[]}     _           p′ = p′
    pos {_ ∷ _}  (inj₁ _)    a  = a
    pos {_ ∷ Σ}  (inj₂ ss′)  p  = pos {Σ} ss′ (lemma {Σ} ss′ p)
      where
      lemma : ∀ {Σ Σ′ ω} ss′ →
              [ Pos (ω ∷ Σ) , Pos Σ′ ]′ ([ inj₁ ∘ inj₂ , inj₂ ]′ (shape′ ss′)) →
              [ Pos Σ , Pos Σ′ ]′ (shape′ ss′)
      lemma {[]}    _           p′  = p′
      lemma {_ ∷ Σ} (inj₁ p)    a   = a
      lemma {_ ∷ Σ} (inj₂ ss′)  _   with shape′ {Σ} ss′
      lemma {_ ∷ Σ} (inj₂ _)    p   | inj₁ _ = p
      lemma {_ ∷ Σ} (inj₂ _)    p′  | inj₂ _ = p′
\end{code}

\begin{code}
⊎⋆→++⋆ :  ∀ {Σ Σ′ X} → (⌊ Σ ⌋^Sig ⊎^C ⌊ Σ′ ⌋^Sig) ⋆^C X → (Σ ++ Σ′) ⋆^S X
⊎⋆→++⋆ = embed m
  where
  m : ∀ {Σ Σ′} → (⌊ Σ ⌋^Sig ⊎^C ⌊ Σ′ ⌋^Sig) ⇒^C ⌊ Σ ++ Σ′ ⌋^Sig
  m {Σ} = record
    { shape     = [ sh-inl , sh-inr {Σ} ]′
    ; position  = λ  { {inj₁ s}   pp′ → pos-inl      s   pp′
                     ; {inj₂ s′}  pp′ → pos-inr {Σ}  s′  pp′
                     }
    }
    where
    sh-inl : ∀ {Σ Σ′} → Sh Σ → Sh (Σ ++ Σ′)
    sh-inl {[]}     ()
    sh-inl {_ ∷ _}  (inj₁ p) = inj₁ p
    sh-inl {_ ∷ _}  (inj₂ s) = inj₂ (sh-inl s)

    sh-inr : ∀ {Σ Σ′} → Sh Σ′ → Sh (Σ ++ Σ′)
    sh-inr {[]}     s′ = s′
    sh-inr {_ ∷ Σ}  s′ = inj₂ (sh-inr {Σ} s′)

    pos-inl : ∀ {Σ Σ′} s → Pos (Σ ++ Σ′) (sh-inl s) → Pos Σ s
    pos-inl {[]}     ()        _
    pos-inl {_ ∷ _}  (inj₁ _)  a = a
    pos-inl {_ ∷ _}  (inj₂ s)  p = pos-inl s p

    pos-inr : ∀ {Σ Σ′} s′ → Pos (Σ ++ Σ′) (sh-inr {Σ} s′) → Pos Σ′ s′
    pos-inr {[]}     _   p′  = p′
    pos-inr {_ ∷ Σ}  s′  p   = pos-inr {Σ} s′ p
\end{code}
