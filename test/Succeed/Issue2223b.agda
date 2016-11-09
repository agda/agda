{-# OPTIONS --allow-unsolved-metas #-}
module _ where

open import Agda.Primitive

postulate Applicative : ∀ {a b} (F : Set a → Set b) → Set (lsuc a ⊔ b)

record Traversable {a} (T : Set a) : Set (lsuc a) where
  constructor mkTrav
  field traverse : ∀ {F} {{AppF : Applicative F}} → T → F T
    -- unsolved metas in type of F

postulate
  V     : ∀ {a} → Set a
  travV : ∀ {a} {F : Set a → Set a} {{AppF : Applicative F}} → V → F V

module M (a : Level) where
  TravV : Traversable {a} V
  TravV = mkTrav travV

postulate
  a : Level
  F : Set → Set
  instance AppF : Applicative F

mapM : V → F V
mapM = Traversable.traverse (M.TravV _)
  -- Here we try to cast (TypeChecking.Constraints.castConstraintToCurrentContext)
  -- a level constraint from M talking about the local (a : Level) to the top-level
  -- (empty) context. This ought not result in an __IMPOSSIBLE__.
