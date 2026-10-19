-- Andreas, 2026-09-23, issue #8771, reported by Jonas Höfer.
-- Test case by Claude, shrunk from the original reproducer.
--
-- `checkInternal` brings projection-like functions into post-fix form,
-- but used to hand the rebuilt term back in that form.  With-abstraction
-- then produced a type in which the same subterm `⟨ Aᵖ a ⟩` occurred both
-- as `Def ⟨_⟩ [Aᵖ a]` and as `Aᵖ a .⟨_⟩`, which the conversion checker
-- could not relate:
--
--   error: [UnequalTypes]
--   The type ⟨ Aᵖ a ⟩ is not a subtype of ⟨ Aᵖ a ⟩
--   because: one is a variable, the other a definition

module Issue8771 where

open import Agda.Primitive
open import Agda.Builtin.Sigma

_×_ : {ℓ ℓ' : Level} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ A λ _ → B

record Unit {ℓ} : Set ℓ where

-- A no-eta record, so that ⟨_⟩ is stuck on neutral arguments.
record Prp (ℓ : Level) : Set (lsuc ℓ) where
  no-eta-equality
  pattern
  constructor _,_
  field
    P   : Set ℓ
    prp : Set ℓ

Prp₀ : Set₁
Prp₀ = Prp lzero

-- ⟨_⟩ is a projection-like function.
⟨_⟩ : {ℓ : Level} → Prp ℓ → Set ℓ
⟨ A , _ ⟩ = A

⊤ᵖ : {ℓ : Level} → Prp ℓ
⊤ᵖ = Unit , Unit

_×ᵖ_ : {ℓ ℓ' : Level} (A : Prp ℓ) (B : Prp ℓ') → Prp (ℓ ⊔ ℓ')
A ×ᵖ B = (⟨ A ⟩ × ⟨ B ⟩) , (⟨ A ⟩ × ⟨ B ⟩)

Πᵖ : {ℓ ℓ' : Level} (A : Set ℓ) (B : A → Prp ℓ') → Prp (ℓ ⊔ ℓ')
Πᵖ A B = ((a : A) → ⟨ B a ⟩) , ((a : A) → ⟨ B a ⟩)

-- A CwF-style context, type and term.

record Cxt (ℓ : Level) : Set (lsuc ℓ) where
  field
    S : Set ℓ
    P : S → Prp ℓ

record Ty {ℓ : Level} (Γ : Cxt ℓ) (ℓ' : Level) : Set (ℓ ⊔ lsuc ℓ') where
  field
    S : Γ .Cxt.S → Set ℓ'
    P : (γ : Γ .Cxt.S) → S γ → Prp ℓ'

record Tm {ℓ ℓ' : Level} (Γ : Cxt ℓ) (A : Ty Γ ℓ') : Set (ℓ ⊔ lsuc ℓ') where
  field
    S : (γ : Γ .Cxt.S) → A .Ty.S γ
    -- NB: the type of P mentions S
    P : (γ : Γ .Cxt.S) (γᵖ : ⟨ Γ .Cxt.P γ ⟩) → ⟨ A .Ty.P γ (S γ) ⟩

Γ₀ : Cxt (lsuc lzero)
Γ₀ .Cxt.S = Σ (Set lzero) λ A → (A → Prp₀)
Γ₀ .Cxt.P _ = ⊤ᵖ

A₀ : Ty Γ₀ lzero
A₀ .Ty.S (A , Aᵖ) = A
A₀ .Ty.P (A , Aᵖ) a = Aᵖ a

B₀ : Ty Γ₀ (lsuc lzero)
B₀ .Ty.S γ = Σ (Σ (Set lzero) λ B → (B → Prp₀)) λ c → (A₀ .Ty.S γ → c .fst)
B₀ .Ty.P γ (c , f) =
  ⊤ᵖ ×ᵖ Πᵖ (A₀ .Ty.S γ) λ a → Πᵖ ⟨ A₀ .Ty.P γ a ⟩ λ _ → c .snd (f a)

postulate
  resize : {ℓ : Level} (P : Prp ℓ) → Prp₀

lemma : (A : Prp₀) (Aᵖ : ⟨ A ⟩ → Prp₀) →
        Σ Prp₀ λ B → Σ (⟨ A ⟩ → ⟨ B ⟩) λ fwd → Σ (⟨ B ⟩ → Prp₀) λ Bᵖ →
          ((a : ⟨ A ⟩) → ⟨ Aᵖ a ⟩ → ⟨ Bᵖ (fwd a) ⟩)
lemma A Aᵖ = resize A , fwd , Bᵖ , fwd'
  where
    postulate
      fwd  : ⟨ A ⟩ → ⟨ resize A ⟩
      Bᵖ   : ⟨ resize A ⟩ → Prp₀
      fwd' : (a : ⟨ A ⟩) → ⟨ Aᵖ a ⟩ → ⟨ Bᵖ (fwd a) ⟩

-- Both copattern clauses abstract over the same `with`-expression.
t : Tm Γ₀ B₀
t .Tm.S (A , Aᵖ) with lemma (A , A) Aᵖ
... | (B , pB) , fwd , Bᵖ , fwd' = (B , Bᵖ) , fwd
t .Tm.P (A , Aᵖ) with lemma (A , A) Aᵖ
... | (B , pB) , fwd , Bᵖ , fwd' = λ γᵖ → record{} , fwd'
