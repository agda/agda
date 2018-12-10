variable A : Set

f : A
f = {!!}

-- The goal type should be printed as A, not A₁.
-- Introducing the hidden variable with C-c C-c should choose name A.
