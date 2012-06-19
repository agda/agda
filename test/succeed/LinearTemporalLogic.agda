{-# OPTIONS --copatterns #-}
-- {-# OPTIONS -v tc.pos:20 -v tc.meta.eta:100 #-}
-- {-# OPTIONS -v tc.lhs:100 #-}

module LinearTemporalLogic where

import Common.Level

record Stream (A : Set) : Set where
  coinductive
  field head : A
        tail : Stream A

-- Stream properties
Proposition : Set → Set₁
Proposition A = Stream A → Set

Now : {A : Set} → (A → Set) → Proposition A
Now P s = P (Stream.head s)

-- Next time
◌ : {A : Set} → Proposition A → Proposition A
◌ P s = P (Stream.tail s)

-- Forever
record ▢ {A : Set} (P : Proposition A) (s : Stream A) : Set where
  coinductive
  field head : P s
        tail : ◌ (▢ P) s

-- Sometimes
data ◇ {A : Set} (P : Proposition A) (s : Stream A) : Set where
  now   : P s → ◇ P s
  later : ◌ (◇ P) s → ◇ P s

-- Infinitely often
▢◇ : {A : Set} → Proposition A → Proposition A
▢◇ P = ▢ (◇ P)

-- Next inf. often  implies inf. often
◌▢◇⇒▢◇ : {A : Set}{P : Proposition A}{s : Stream A} →
    ◌ (▢◇ P) s → ▢◇ P s
▢.head (◌▢◇⇒▢◇ f) = later (▢.head f)
▢.tail (◌▢◇⇒▢◇ f) = ◌▢◇⇒▢◇ (▢.tail f)

-- Forever implies inf. oft.
▢⇒▢◇ : {A : Set}{P : Proposition A}{s : Stream A} →
    ▢ P s → ▢◇ P s
▢.head (▢⇒▢◇ f) = now (▢.head f)
▢.tail (▢⇒▢◇ f) = ▢⇒▢◇ (▢.tail f)

-- Eventually
◇▢ : {A : Set} → Proposition A → Proposition A
◇▢ P = ◇ (▢ P)

-- Eventually implies inf. oft.
◇▢⇒▢◇ : {A : Set}{P : Proposition A}{s : Stream A} →
  ◇▢ P s → ▢◇ P s
◇▢⇒▢◇ (now forever) = ▢⇒▢◇ forever
◇▢⇒▢◇ (later event) = ◌▢◇⇒▢◇ (◇▢⇒▢◇ event)

-- We now prove that inf. oft. does not imply eventually
-- by exhibiting a counter example

data ⊥ : Set where
record ⊤ : Set where
  constructor tt

data Bool : Set where
  true false : Bool

True : Bool → Set
True true = ⊤
True false = ⊥

open Stream

alternate : Stream Bool
(     (head alternate)) = true
(head (tail alternate)) = false
(tail (tail alternate)) = alternate

-- alternate contains infinitely many 'true's
thm1 : ▢◇ (Now True) alternate
(        (▢.head thm1)) = now tt
(▢.head (▢.tail thm1)) = later (now tt)
(▢.tail (▢.tail thm1)) = thm1

-- alternate does not eventually contain only 'true's
mutual

  thm2 : ◇▢ (Now True) alternate → ⊥
  thm2 (now forever⊤) = ▢.head (▢.tail forever⊤)
  thm2 (later event)  = thm2′ event

  thm2′ : ◇▢ (Now True) (tail alternate) → ⊥
  thm2′ (now forever⊤) = ▢.head forever⊤
  thm2′ (later event)  = thm2 event
