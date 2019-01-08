-- A minor variant of code reported by Andreas Abel.

-- Andreas, 2011-10-04
--
-- Agda's coinduction is incompatible with initial algebras
--
-- Sized types are needed to formulate initial algebras in general:
--
{-# OPTIONS --sized-types --no-guardedness #-}
--
-- We need to skip the positivity check since we cannot communicate
-- to Agda that we only want strictly positive F's in the definition of Mu
--
{-# OPTIONS --no-positivity-check #-}
--
module _ where

open import Agda.Builtin.Coinduction renaming (∞ to co)
open import Agda.Builtin.Size

-- initial algebras

data Mu (F : Set → Set) : Size → Set where
  inn : ∀ {i} → F (Mu F i) → Mu F (↑ i)

iter : ∀ {F : Set → Set}
         (map : ∀ {A B} → (A → B) → F A → F B)
         {A} → (F A → A) → ∀ {i} → Mu F i → A
iter map s (inn t) = s (map (iter map s) t)

-- the co functor (aka Lift functor)

F : Set → Set
F A = co A

map : ∀ {A B : Set} → (A → B) → co A → co B
map f a = ♯ f (♭ a)

-- the least fixed-point of co is inhabited

bla : Mu F ∞
bla = inn (♯ bla)

-- and goal!

data ⊥ : Set where

false : ⊥
false = iter map ♭ bla

-- note that co is indeed strictly positive, as the following
-- direct definition of Mu F ∞ is accepted

data Bla : Set where
  c : co Bla → Bla

{- -- if we inline ♭ map into iter, the termination checker detects the cheat
iter' : Bla → ⊥
iter' (c t) = ♭ (♯ iter' (♭ t))
-- iter' (c t) = ♭ (map iter' t)
-}

-- Again, I want to emphasize that the problem is not with sized types.
-- I have only used sized types to communicate to Agda that initial algebras
-- (F, iter) are ok.  Once we have initial algebras, we can form the
-- initial algebra of the co functor and abuse the guardedness checker
-- to construct an inhabitant in this empty initial algebra.
--
-- Agda's coinduction mechanism confuses constructor and coconstructors.
-- Convenient, but, as you have seen...
