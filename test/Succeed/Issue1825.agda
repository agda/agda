-- Andreas, 2016-02-09, issue reported by Anton Setzer
-- {-# OPTIONS -v tc.conv.infer:30 -v tc.deftype:30 #-}

{-# OPTIONS --allow-unsolved-metas #-}

data ⊥ : Set where

data MaybeSet : Set₁ where
  nothing : MaybeSet
  just : Set → MaybeSet

-- not injective
FromJust : MaybeSet → Set
FromJust nothing = ⊥
FromJust (just A) = A

R0 : ⊥ → Set
R0 ()

data C1 (A :  Set) : Set where
  c1 : ⊥ → C1 A

-- R1 is projection-like
R1 : (A : Set) → C1 A → Set
R1 A (c1 c) = R0 c
-- R1 A (c1 ()) -- no int. err.

record Iface  : Set₁ where
  field
    Command   : Set
    Response  : Command → Set

I1 : (A : Set) → Iface
Iface.Command   (I1 A) = C1 A
Iface.Response  (I1 A) = R1 A
-- Iface.Response  (I1 A) (c1 c) = R0 c -- no int.err.
-- I1 A = record { Command = C1 A; Response = R1 A } -- no. int. err

postulate
  IO : Iface → Set

data C2 (s : MaybeSet) : Set₁ where
  c2  : (FromJust s → IO (I1 (FromJust s))) → C2 s

data IOˢ : MaybeSet → Set₁ where
  act : {s : MaybeSet} (c : C2 s) → IOˢ s

postulate
  bla : Set → ⊥ → IO (I1  ⊥)

test : IOˢ nothing
test = act (c2 (bla {!!}))
