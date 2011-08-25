{- This example goes through now that we allow instantiation of
   blocked terms #-}
module Issue439 where

record Σ (A : Set) (B : A → Set) : Set where
 constructor _,_
 field
   p₁ : A
   p₂ : B p₁

open Σ

record ⊤ : Set where

data Tree : Set where
 leaf : Tree
 node : Tree → Tree → Tree

mutual

 U : Tree → Set
 U leaf           = ⊤
 U (node tr₁ tr₂) = Σ (U tr₁) λ a → El a → U tr₂

 El : ∀ {tr} → U tr → Set
 El {leaf}         _       = ⊤
 El {node tr₁ tr₂} (a , b) = (x : El a) → El (b x)

mutual

 data C : Set where
   c : (Γ : C) → T Γ → C

 T : C → Set
 T Γ = Σ Tree (λ tr → E Γ → U tr)

 E : C → Set
 E (c Γ σ) = Σ (E Γ) λ γ → El (p₂ σ γ)

postulate
 e : C
 M : (Γ : C) → T Γ → Set
 z : ∀ {Γ σ} → M (c Γ σ) (p₁ σ , λ γ → p₂ σ (p₁ γ))
 l : ∀ {Γ} σ {τ} → M (c Γ σ) τ →
     M Γ (_ , λ γ → p₂ σ γ , λ v → p₂ τ (γ , v))
 a : ∀ {Γ tr₁ tr₂ σ} →
     M Γ (node tr₁ tr₂ , σ) → M Γ (tr₁ , λ γ → p₁ (σ γ)) →
     M Γ (leaf , _)
 s : ∀ {Γ} → M Γ (leaf , _)

t : ∀ {Γ σ} → M Γ σ → T Γ
t {σ = σ} _ = σ

foo : M (c e (leaf , _)) (leaf , _)
foo = a (l (t s) z) z
