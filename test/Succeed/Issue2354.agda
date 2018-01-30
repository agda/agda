-- Andreas, 2016-12-22, issue #2354
-- Interaction between size solver, constraint solver, and instance search.

-- The instance search fails initially because of a non rigid meta.
-- Before freezing, there is another attempt.
-- The instance search succeeds and instantiates the meta for M.
-- Then, a size constraint is solved which had blocked a term.
-- Finally the blocking constraint can be resolved.

-- Thus, we need to
-- * wake constraints
-- * solve size constraints
-- * wake constraints again.
-- In principle, there could be many alternations needed!?

-- {-# OPTIONS -v tc.meta:30 -v tc.instance:30 -v tc.constr:50 -v tc.size:30 -v tc.decl:10 #-}
-- {-# OPTIONS -v tc.instance:30 -v tc.decl:20 #-}
-- {-# OPTIONS -v tc.instance.rigid:100 -v tc.instance:70 -v tc.size:30 #-}
-- {-# OPTIONS -v tc.term.con:50 #-}

{-# BUILTIN SIZEUNIV SizeU #-}
{-# BUILTIN SIZE     Size   #-}
{-# BUILTIN SIZELT   Size<_ #-}
{-# BUILTIN SIZESUC  ↑_     #-}
{-# BUILTIN SIZEINF  ∞      #-}

record ⊤ : Set where
  constructor tt

record RawMonad (M : Set → Set) : Set₁ where
  field return : ∀{A} → A → M A

mutual
  data Delay (i : Size) (A : Set) : Set where
    now : A → Delay i A
    later : Delay∞ i A → Delay i A

  record Delay∞ (i : Size) (A : Set) : Set where
    coinductive
    field force : ∀ {j : Size< i} → Delay j A

instance
  RawMonad-Delay : ∀ {i} → RawMonad (Delay i)
  RawMonad-Delay = record
    { return = Delay.now
    }

open RawMonad {{...}}

test : ∀ {i} → Delay i ⊤
test {i} = return tt  -- Solution: return {{RawMonad-Delay {i}}} tt

-- Should find solution!
