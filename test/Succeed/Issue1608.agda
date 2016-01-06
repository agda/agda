postulate
  C : Set
  anything : C

record I : Set where
  constructor c
  field
    {f} : C

data Wrap : (i : I) → Set where
  wrap : ∀ {i} → Wrap i

works : ∀ {j} → Wrap j → C
works {c {._}} (wrap {c {x}}) = anything

fails : ∀ {j} → Wrap j → C
fails {c {._}} (wrap {c}) = anything

-- Failed to infer the value of dotted pattern
-- when checking that the pattern ._ has type C

fails' : ∀ {j} → Wrap j → C
fails' .{c {_}} (wrap {c}) = anything

works2 : ∀ {j} → Wrap j → C
works2 {c} (wrap {c {._}}) = anything

fails2 : ∀ {j} → Wrap j → C
fails2 {c {._}} (wrap {c}) = anything
