-- Andreas, Ulf, 2016-06-01, discussing issue #679
-- {-# OPTIONS -v tc.with.strip:20 #-}

postulate anything : {A : Set} → A

data Ty : Set where
  _=>_ : (a b : Ty) → Ty

⟦_⟧ : Ty → Set
⟦ a => b ⟧ = ⟦ a ⟧ → ⟦ b ⟧

eq : (a : Ty) → ⟦ a ⟧ → ⟦ a ⟧ → Set
eq (a => b) f g = ∀ {x y : ⟦ a ⟧} → eq a x y → eq b (f x) (g y)

bad : (a : Ty) (x : ⟦ a ⟧) → eq a x x
bad (a => b) f h with b
bad (a => b) f h | _ = anything
-- ERROR WAS: Too few arguments in with clause!
-- Should work now.
