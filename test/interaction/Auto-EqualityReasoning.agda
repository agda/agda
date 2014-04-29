module Auto-EqualityReasoning where

-- equality reasoning, computation and induction

open import Auto.Prelude


module AdditionCommutative where

 lemma : ∀ n m → (n + succ m) ≡ succ (n + m)
 lemma n m = {!-c!}  -- h0
{-
 lemma zero m = refl
 lemma (succ x) m = cong succ (lemma x m)
-}

 lemma' : ∀ n m → (n + succ m) ≡ succ (n + m)
 lemma' zero m = refl
 lemma' (succ n) m = cong succ (lemma' n m)

 addcommut : ∀ n m → (n + m) ≡ (m + n)
 addcommut n m = {!-c lemma'!}  -- h1
{-
 addcommut zero zero = refl
 addcommut zero (succ x) = sym (cong succ (addcommut x zero))  -- solution does not pass termination check
 addcommut (succ x) m = begin (succ (x + m) ≡⟨ cong succ (addcommut x m) ⟩ (succ (m + x) ≡⟨ sym (lemma' m x) ⟩ ((m + succ x) ∎)))
-}

