-- 2015-05-05 Bad error message

_=R_ : Rel → Rel → Set
R =R S : (R ⊆ S) × (S ⊆ R) -- here is a typo, : instead of =

ldom : Rel → Pred
ldom R a = ∃ λ b → R a b

-- More than one matching type signature for left hand side ldom R a
-- it could belong to any of: ldom R
