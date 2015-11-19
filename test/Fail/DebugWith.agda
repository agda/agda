-- Andreas, 2015-11-18 Fixing de Bruijn indices in debug print for with.

{-# OPTIONS -v tc.with.top:25 #-}  -- KEEP!

postulate
  Trash A : Set
  P : A → Set
  provokeError : Trash

-- The trash arguments should not show up in the debug printing!
-- If they do, permutations or de Bruijn indices are messed up,
-- or the debug messages are printed in the wrong context.
test : (trash1 : Trash) (b : A) (trash2 : Trash) (f : ∀ x → P x) (trash3 : Trash) → Set
test trash1 b trash2 f trash3 with f b
... | p = provokeError

-- EXPECTED:
-- ...
-- vs     = [f b]
-- as     = [P b]
-- ...
--     with arguments [f b]
--              types [P b]
-- ...
-- checkWithFunction
-- ...
--   as     = [P b]
--   vs     = [f b]
-- ...
--
-- and then a type error message.
