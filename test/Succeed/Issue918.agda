{-
Reported by sattler.christian, Oct 10 (3 days ago)

This is a funny one. The below code snippet produces the following error under the current Agda development version:

An internal error has occurred. Please report this as a bug.
Location of the error: src/full/Agda/TypeChecking/Eliminators.hs:85

Note the spurious Tm datatype that isn't used anywhere? Remove it, move its declaration forward, or its definition backward, and the internal error vanishes, leaving a few yellow spots.

Now uncomment the two implicit arguments at the bottom of the code. All metavars are now resolved. Now put the Tm datatype back in - yellow spots reappear, but different from before!
-}

{-# OPTIONS --cubical-compatible #-}
module Issue918 where

record ⊤ : Set where
  constructor tt

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ


_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

_+'_ : ℕ → ℕ → ℕ
i +' zero  = i
i +' suc j = suc i +' j


U : ℕ → Set
U zero    = ⊤
U (suc n) = Σ (U n) (λ _ → ⊤)

V : ℕ → Set
V zero    = ⊤
V (suc m) = Σ ⊤ (λ _ → V m)

combine : {i j : ℕ} → Σ (U i) (λ _ → V j) → U (i +' j)
combine {j = zero}  = λ {(A , _) → A}
combine {j = suc j} = combine {j = j} ∘ (λ {(Γ , (A , T)) → ((Γ , A) , T)})

data Tm : Set

ctx-hom : (m : ℕ) → U m → Set
ctx-hom zero    _       = ⊤
ctx-hom (suc m) (Δ , _) = Σ (ctx-hom m Δ) (λ _ → ⊤)

ctx-hom-split-iso : {m k : ℕ} {Δ : U m} {T : V k}
                  → ctx-hom (m +' k) (combine (Δ , T))
                  → Σ (ctx-hom m Δ) (λ _ → V k)
ctx-hom-split-iso {k = zero}  = λ Δ → (Δ , tt)
ctx-hom-split-iso {m} {k = suc k} {Δ} {(A , T)} =
    ((λ {((Γ , A) , T) → (Γ , (A , T))}))
  ∘ ctx-hom-split-iso {m = suc m} --{Δ = (Δ , A)}

data Tm where



{- Project Member #1 andreas.m.abel

That was quite a riddle to solve.

1. The internal error is actually triggered in the termination checking phase.
   I fixed this, will push soon.
   A workaround is --no-termination-check

2. The data-Tm-brace puts ctx-hom and ctx-hom-split-iso into a mutual block.
   This prevents ctx-hom to be unfolded during checking the -split-iso.
   You can achieve the same by explicitely putting the two defs into a mutual
   block.
   If the mutual block is removed, the yellow stuff appears.
   HO-unification is sensitive to reduction, at this moment I do not see an
   easy fix for this behavior.

3. "yellow spots reappear, but in different places"  I could not replay this.
   For me, the yellow only disappeared if I also gave {T = T}, but then
   it consistently disappears and reappears when putting in and out of a mutual
   block.

-}
