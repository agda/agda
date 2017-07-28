-- Andreas, 2017-07-29, issue #2644 reported by Christian Sattler
--
-- Silly mistake in expandRecordVar:
-- Substitution applied to ListTel instead of Telescope.
-- (Messed up the de Bruijn indices, garbage.)

-- This file should pass with lots of yellow.

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v tc.meta.assign.proj:45 #-}

-- OLD:
-- {-# OPTIONS -v tc.cc:20 #-}
-- {-# OPTIONS -v tc.lhs:10 #-}
-- {-# OPTIONS -v tc.decl:10 #-}
-- {-# OPTIONS -v tc.ip:20 #-}
-- {-# OPTIONS -v tc.check.internal:20 #-}
-- {-# OPTIONS -v tc.meta.check:30 #-}
-- {-# OPTIONS -v tc:20 #-}
-- {-# OPTIONS -v tc.meta:50 #-}
-- {-# OPTIONS -v tc:45 #-}
-- {-# OPTIONS -v tc.term.exlam:100 -v tc:90 #-}

record Σ (A¹ : Set) (B¹ : A¹ → Set) : Set where
  constructor pair
  field
    fst : A¹
    snd : B¹ fst
open Σ

postulate
  Path : (A² : Set) → A² → A² → Set
  path : (A³ : Set) → Path _ _ _

record S : Set₁ where
  constructor mkS
  field
    Aₛ : Set
    Bₛ : (aₛ¹ : Aₛ) → Set
    zₛ : (aₛ² : Aₛ) → Bₛ aₛ²

record T : Set₁ where
  constructor mkT
  field
    A : Set
    B : (a¹ : A) → Set
    z : (a² : A) → B a²
    s : (a³ : A) → B a³ → B a³
    p : (a⁴ : A) (f : B a⁴) → Path _ f (s _ (z _))

-- passes without the matching
f₀ : S → T
f₀ X = record { A = Σ _ _
             ; B =  λ b → Σ _ _ -- λ { (b₁ , b₂) → Σ _ _ }
             ; z =  λ z₁ → pair (S.zₛ X _) _
             ; s =  λ s₁ s₂ → _
             ; p =  λ p₁ p₂ → path _
             }


-- This was my final variant

module Final where
 mutual
  TA : S → Set
  TA Z = Σ _ _
  aux : (Y : S) → TA Y → Set
  aux Y (pair b¹ b²) = Σ _ _  -- fails
  fₐ : S → T
  fₐ X = record { A = TA X
                ; B =  aux X
                ; z =  λ (z¹ : TA X) → pair (S.zₛ X _) _
                ; s =  λ (s¹ : TA X) (s² : aux X s¹) → _
                ; p =  λ (p¹ : TA X) (p² : aux X p¹) → path _
                }

-- Intermediate

fₐᵤ : S → T
fₐᵤ X = record { A = TA
              ; B =  aux
              ; z =  λ (z₁ : TA) → pair (S.zₛ X _) _
              ; s =  λ (s₁ : TA) (s₂ : aux s₁) → _
              ; p =  λ (p₁ : TA) (p₂ : aux p₁) → path _
              }
  where
  TA = Σ _ _
  aux : TA → Set
  -- (passes without the matching)
  -- aux b = let b₁ = fst b; b₂ = snd b in {! Σ _ _ !}  -- worked
  aux (pair b₁ b₂) = Σ _ _  -- failed

-- Close to original

f : S → T
f X = record { A = Σ _ _
             ; B =  λ { (pair b₁ b₂) → Σ _ _ }
             ; z =  λ z₁ → pair (S.zₛ X _) _
             ; s =  λ s₁ s₂ → _
             ; p =  λ p₁ p₂ → path _
             }



{- Hunted down the crash cause:

context before projection expansion
  (X : S) (p¹ : TA X) (p² : aux X p¹)
meta args:  [X, p¹, pair (S.zₛ X (_aₛ²_34 X p¹)) (?1 X p¹)]
trying to expand projected variable X
eta-expanding var  X  in terms  ([X, p¹,
                                  pair (S.zₛ X (_aₛ²_34 X p¹)) (?1 X p¹)],_8 (?2 X p¹ p²))
meta args:  [mkS Aₛ(X) Bₛ(X) zₛ(X), p¹,
             pair (zₛ(X) (_aₛ²_34 (mkS Aₛ(X) Bₛ(X) zₛ(X)) p¹))
             (?1 (mkS Aₛ(X) Bₛ(X) zₛ(X)) p¹)]
context before projection expansion
  (X : S)           S
  (p¹ : TA X)       TA 0
  (p² : aux X p¹)   aux 1 0
context after projection expansion
  (Aₛ(X) : Set)
  (Bₛ(X) : Aₛ(X) → Set)
  (zₛ(X) : (aₛ² : Aₛ(X)) → Bₛ(X) aₛ²)
  (p¹ : TA (mkS Aₛ(X) Bₛ(X) zₛ(X)))      -- This type is fine
  (p² : aux Aₛ(X) (mkS Bₛ(X) zₛ(X) p¹))  -- This type is messed up!

-}

-- -}
-- -}
-- -}
-- -}
-- -}
