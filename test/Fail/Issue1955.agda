
data unit : Set where tt : unit

record Y (A : Set) : Set where field y : A
record Z (A : Set) : Set where field z : A

instance
  -- Y[unit] : Y unit
  -- Y.y Y[unit] = tt
  Z[unit] : Z unit
  Z.z Z[unit] = tt

foo : ∀ (A : Set) {{YA : Y A}} {{ZA : Z A}} → unit
foo A = tt

foo[unit] : unit
foo[unit] = foo unit -- {{ZA = Z[unit]}}
