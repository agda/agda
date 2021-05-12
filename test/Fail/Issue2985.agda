-- Andreas, 2018-03-03, termination bug found by Nisse
-- caused by a missing call to `instantiate`.

-- {-# OPTIONS -vtc:20 -vterm:20 #-}

{-# OPTIONS --sized-types #-}

{-# BUILTIN SIZEUNIV SizeU #-}
{-# BUILTIN SIZE     Size   #-}
{-# BUILTIN SIZELT   Size<_ #-}
{-# BUILTIN SIZEINF  ∞      #-}

record Unit (i : Size) : Set where
  coinductive
  field
    force : (j : Size< i) → Unit j

postulate
  tail : Unit ∞ → Unit ∞
  id   : ∀ i → Unit i → Unit i

u : ∀ i → Unit i
u i = tail (id _ λ { .Unit.force j → u j })

-- Should not termination check.
