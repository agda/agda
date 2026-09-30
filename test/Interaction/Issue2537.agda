-- Andreas, 2017-04-10, issue #2537 reported by xekoukou
-- Preserve named args when splitting in a where clause.

-- {-# OPTIONS -v reify:100 #-}

data Bool : Set where
  true false : Bool

fun : {a b c d e f g : Bool} → Bool → Bool
fun {g = g} x with x
... | r = {!g!} -- C-c C-c g

-- Expected result:
-- fun {g = true} x | r = ?
-- fun {g = false} x | r = ?
