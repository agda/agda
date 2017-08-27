
postulate
  C : Set
  anything : C

record I : Set where
  constructor c
  field
    f : C

data Wrap : (j : I) → Set where
  wrap : ∀ {j} → Wrap j

-- The following should not pass.
-- It did before the fix of #142.
issue142 : ∀ {j} → Wrap j → C
issue142 {c _} (wrap {c _}) with anything
issue142 {c _} (wrap .{c anything}) | z = z
