{-# OPTIONS --allow-unsolved-metas --universe-polymorphism #-}

module Issue203 where

postulate
  Level : Set
  zero : Level
  suc  : Level → Level
  max : Level → Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC suc #-}
{-# BUILTIN LEVELMAX max #-}

-- Should work but give unsolved metas (type of b)
data ↓ {a b} (A : Set a) : Set a where
  [_] : (x : A) → ↓ A

mutual -- avoid freezing

  -- Shouldn't instantiate the level of Σ to a
  data Σ {a b} (A : Set a) (B : A → Set b) : Set _ where
    _,_ : (x : A) (y : B x) → Σ A B
  
  instantiateToMax : ∀ {a b}(A : Set a)(B : A → Set b) → Set (max a b)
  instantiateToMax = Σ
    
