-- {-# OPTIONS -v tc.with:50 #-}
module Issue295 where

data ⊥ : Set where

data Arr : Set where
  _⟶_ : ⊥ → ⊥ → Arr

_﹔_ : Arr → Arr → Arr
(a ⟶ b)﹔(c ⟶ d) with b
... | ()

data Fun : Arr → Set where
  ∙ : ∀ a b c d → Fun (a ⟶ b) → Fun (c ⟶ d) → Fun ((a ⟶ b)﹔(c ⟶ d))

f : ∀ a b c d e f → Fun (a ⟶ b) → Fun (c ⟶ d) → Fun (e ⟶ f)
f a b c d e f F G = ∙ a b c d F G

-- The problem does not appear to be restricted to the pretty-printer.
-- With -v10 I get the following output:
--
-- compareTerm (a ⟶ b) ﹔ (b ⟶ c) == a ⟶ c : Arr
-- { compareAtom
-- compareAtom (b ⟶ a) ﹔ (c ⟶ b) | b == a ⟶ c : Arr
-- /tmp/Bug.agda:16,15-28
-- (b ⟶ a) ﹔ (c ⟶ b) | b != a ⟶ c of type Arr
-- when checking that the expression ∙ a b b c F G has type
-- Fun (a ⟶ c)
