-- Andreas, 2017-05-24, issue #2590
-- Making variables visible by case splitting in with-clauses

-- {-# OPTIONS -v interaction.case:20 #-}
-- {-# OPTIONS -v reify:100 #-}
-- {-# OPTIONS -v tc.display:100 #-}

open import Agda.Builtin.Nat

test1 : {x : Nat} → Nat
test1 with Set
... | q = {!.x!}  -- C-c C-c

-- Expected result:
-- test1 {x} | q = ?

data Any (x : Nat) : Set where
  any : Any x

postulate
  zonk : ∀{x} → Any x → Nat

test2 : {x y : Nat} → Any y → Nat
test2 p with zonk p
... | q = {!.y!} -- C-c C-c

-- Expected result:
-- test2 {y = y} p | q = ?
