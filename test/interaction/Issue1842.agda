-- Issue #1842, __IMPOSSIBLE__ showed up in debug output

{-# OPTIONS -v interaction.case:65 #-} -- KEEP

data Bool : Set where
  true false : Bool

test : Bool → Bool
test x = {!x!} -- C-c C-c

-- Splitting here with debug output turned on
-- should not crash.
