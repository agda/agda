-- Andreas, 2014-04-11, issue reported by James Chapman
-- {-# OPTIONS -v tc.decl.ax:100 #-}
-- {-# OPTIONS -v tc.polarity:100 #-}
{-# OPTIONS --copatterns --sized-types #-}
module _ where

open import Common.Size

module Works where
  mutual
    data Delay i (A : Set) : Set where
      now   : A → Delay i A
      later : ∞Delay i A → Delay i A

    record ∞Delay i A : Set where
      coinductive
      field force : {j : Size< i} → Delay j A
  open ∞Delay

  mutual
    _=<<_ : ∀{i A B} → Delay i A → (A → Delay i B) → Delay i B
    now x   =<< f = f x
    later x =<< f = later (x ∞=<< f)

    _∞=<<_ : ∀{i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (c ∞=<< f) = force c =<< f

-- Polarity of Issue1099.Delay from positivity: [Contravariant,Covariant]
-- Refining polarity with type  Size → Set → Set
-- Polarity of Issue1099.Delay: [Contravariant,Covariant]

module Fails where
  mutual
    data Delay i (A : Set) : Set where
      now   : A → Delay i A
      later : ∞Delay i A → Delay i A

    record ∞Delay i A : Set where
      coinductive
      field force : {j : Size< i} → Delay j A
  open ∞Delay

  mutual
    _=<<_ : ∀{i A B} → Delay i A → (A → Delay i B) → Delay i B
    now x   =<< f = f x
    later x =<< f = later (x ∞=<< f)

    _∞=<<_ : ∀{i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (c ∞=<< f) = force c =<< f

-- Polarity of Issue1099.Delay from positivity: [Contravariant,Covariant]
-- Refining polarity with type  (i₁ : Size) → Set → Set
-- WAS: Polarity of Issue1099.Delay: [Invariant,Covariant]
-- NOW: Polarity of Issue1099.Delay: [Contravariant,Covariant]

-- Polarity refinement calls free variable analysis, which is not in the
-- monad.  Thus, need to instantiate metas before polarity refinement.
