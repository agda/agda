-- Andreas, 2019-03-28, issue #3248, reported by guillaumebrunerie

{-# OPTIONS --sized-types --show-implicit #-}

-- {-# OPTIONS -v tc:10 #-}
-- {-# OPTIONS -v tc.term:20 #-}
-- {-# OPTIONS -v tc.conv.size:45 #-}
-- {-# OPTIONS -v tc.conv.coerce:45 #-}
-- {-# OPTIONS -v tc.term.args.target:45 #-}

{-# BUILTIN SIZEUNIV SizeUniv #-}  --  SizeUniv : SizeUniv
{-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
{-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
{-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
{-# BUILTIN SIZEINF  ∞        #-}  --  ∞        : Size
{-# BUILTIN SIZEMAX  _⊔ˢ_     #-}  --  _⊔ˢ_     : Size → Size → Size

data D (i : Size) : Set where
  c : {j : Size< i} → D j → D i

f : {i : Size} → D i → D i → D i
f  (c {j₁} l1)
   (c {j₂} l2) = c {j = j₁ ⊔ˢ j₂} (f {j₁ ⊔ˢ j₂} l1 l2)

-- The problem was that the new "check target first" logic
-- e49d1ca276e5adbf2eb9f6cd33926b786cef78f7
-- for checking applications does not work for Size<.
--
--   Checking target types first
--     inferred = Size
--     expected = Size< i
--
-- It is not the case that Size <= Size< i, however, coerce succeeds,
-- since e.g. j : Size <= Size< i  if  j : Size< i.
--
-- The solution is to switch off the check target first logic
-- if the target type of a (possibly empty) application is Size< _.
