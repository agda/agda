\subsection{The semantics of well-typed terms}
\label{well-typed-semantics}

\AgdaHide{
\begin{code}
module Issue854.WellTypedSemantics where

open import Level using (lower)
open import Function hiding (_∋_)
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Pointwise hiding (refl)
open import Data.Container.FreeMonad using (rawMonad; inn)
    renaming (_⋆_ to _⋆^C_)
open import Data.W
open import Relation.Binary.PropositionalEquality
open import Category.Monad

open import Data.List.Membership.Propositional
open import Issue854.Types
open import Issue854.Context
open import Issue854.EilenbergMooreAlgebra as EMA
open import Issue854.TypesSemantics
open import Issue854.WellTyped
open import Issue854.Run
open import Issue854.RunCompat
\end{code}
}

\begin{code}
⟦_⟧^var : ∀ {Γ V} → Γ ∋ V → ⟦ Γ ⟧^Ctx → ⟦ V ⟧^VType
⟦ zero   ⟧^var = proj₂
⟦ suc m  ⟧^var = ⟦ m ⟧^var ∘ proj₁

⟦_⟧^con : ∀ {Δ P A} → (P , A) ∈ Δ → ⟦ P ⟧^VType →
         (⟦ A ⟧^VType → ⟦ μ Δ ⟧^VType) → ⟦ μ Δ ⟧^VType
⟦ m ⟧^con p k = sup (sh m p , k ∘ ar m p)

⟦_⟧^op : ∀ {Σ P A} → (P , A) ∈ Σ → (⟦ P ⟧^VType → Σ ⋆^S ⟦ A ⟧^VType)
⟦ m ⟧^op s = inn (sh m s , (M.return ∘ ar m s))
  where
  module M = RawMonad rawMonad

mutual

  ⟦_⟧^v : ∀ {Γ V v} → Γ ⊢^v v ∶ V → ⟦ Γ ⟧^Ctx → ⟦ V ⟧^VType
  ⟦ var m      ⟧^v γ = ⟦ m ⟧^var γ
  ⟦ con m p k  ⟧^v γ = ⟦ m ⟧^con (⟦ p ⟧^v γ) (λ a → ⟦ k ⟧^v (γ , a))
  ⟦ thunk c    ⟧^v γ = ⟦ c ⟧^c γ
  ⟦ ⟨⟩         ⟧^v γ = _
  ⟦ u , v      ⟧^v γ = ⟦ u ⟧^v γ , ⟦ v ⟧^v γ
  ⟦ 𝟘-elim v   ⟧^v γ = ⊥-elim (⟦ v ⟧^v γ)
  ⟦ ι₁ u       ⟧^v γ = inj₁ (⟦ u ⟧^v γ)
  ⟦ ι₂ v       ⟧^v γ = inj₂ (⟦ v ⟧^v γ)

  ⟦_⟧^c : ∀ {Γ C c} → Γ ⊢^c c ∶ C → ⟦ Γ ⟧^Ctx → Carrier ⟦ C ⟧^CType
  ⟦ return v         ⟧^c γ = M.return (⟦ v ⟧^v γ)
    where
    module M = RawMonad rawMonad

  ⟦ _to_ {Σ″ = Σ″}{V = V} c k p q ⟧^c γ = bind ⟦ Σ″ ⋆ V ⟧^CType
    (embed (⊆→⇒ p) (⟦ c ⟧^c γ))
    (λ u → embed (⊆→⇒ q) (⟦ k ⟧^c (γ , u)))

  ⟦ force v          ⟧^c γ = ⟦ v ⟧^v γ
  ⟦ let′ v be k      ⟧^c γ = ⟦ k ⟧^c (γ , ⟦ v ⟧^v γ)
  ⟦ ⟨⟩               ⟧^c γ = M.return _
    where
    module M = RawMonad rawMonad
  ⟦ split p k        ⟧^c γ = let (u , v) = ⟦ p ⟧^v γ in ⟦ k ⟧^c ((γ , u) , v)
  ⟦ π₁ p             ⟧^c γ = proj₁ (⟦ p ⟧^c γ)
  ⟦ π₂ p             ⟧^c γ = proj₂ (⟦ p ⟧^c γ)
  ⟦ b , c            ⟧^c γ = ⟦ b ⟧^c γ , ⟦ c ⟧^c γ
  ⟦ ƛ c              ⟧^c γ = λ v → ⟦ c ⟧^c (γ , v)
  ⟦ f · v            ⟧^c γ = ⟦ f ⟧^c γ (⟦ v ⟧^v γ)
  ⟦ op m             ⟧^c γ = ⟦ m ⟧^op
  ⟦ iter φ v         ⟧^c γ = EMA.iter (lemma (⟦ φ ⟧^cs γ)) (⟦ v ⟧^v γ)
    where
    lemma : ∀ {Δ C} → ⟦ Alg Δ C ⟧^CTypes → ALG ⌊ Δ ⌋^Sig (Carrier ⟦ C ⟧^CType)
    lemma {[]}     _       (()     , _)
    lemma {_ ∷ _}  (f , γ) (inj₁ p , ih)  = f p ih
    lemma {_ ∷ _}  (_ , γ) (inj₂ s , k)   = lemma γ (s , k)

  ⟦ run {Σ′ = Σ′} φ c p q ⟧^c γ i = RUN  {Σ′ = ⌊ Σ′ ⌋^Sig}  (lemma (⟦ φ ⟧^cs γ))
                                         (⇒++→⇒⊎ (⊆→⇒ p)) (⊆→⇒ q) (⟦ c ⟧^c γ) i
    where
    lemma : ∀ {Σ Σ′ Σ″ I U V} → ⟦ PHomo′ Σ Σ′ U I Σ″ V ⟧^CTypes →
            PHOMO′ ⌊ Σ ⌋^Sig ⌊ Σ′ ⌋^Sig ⟦ U ⟧^VType ⟦ I ⟧^VType ⌊ Σ″ ⌋^Sig ⟦ V ⟧^VType
    lemma {[]}     (f , _) (inj₁ u        , _)   i = f u i
    lemma {[]}     (_ , _) (inj₂ ()       , _)   i
    lemma {_ ∷ Σ}  (f , _) (inj₂ (inj₁ p) , ih)  i =
        f p (λ a → let w , w′ = ih a in ⊎⋆→++⋆ w , w′) i
    lemma {_ ∷ Σ}  (_ , g) (inj₁ u        , k)   i = lemma {Σ} g (inj₁ u , k) i
    lemma {_ ∷ Σ}  (_ , g) (inj₂ (inj₂ s) , k)   i = lemma {Σ} g (inj₂ s , k) i

  ⟦_⟧^cs : ∀ {Γ Cs cs} → Γ ⊢^cs cs ∶ Cs → ⟦ Γ ⟧^Ctx → ⟦ Cs ⟧^CTypes
  ⟦ []      ⟧^cs γ = _
  ⟦ c ∷ cs  ⟧^cs γ = ⟦ c ⟧^c γ , ⟦ cs ⟧^cs γ
\end{code}

Remark: assuming the meta-theory is strongly normalising, we get...?
