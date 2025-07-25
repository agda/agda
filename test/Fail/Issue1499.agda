-- 2015-05-05 Bad error message

_=R_ : Rel → Rel → Set
R =R S : (R ⊆ S) × (S ⊆ R) -- here is a typo, : instead of =

ldom : Rel → Pred
ldom R a = ∃ λ b → R a b

-- Error WAS:
-- More than one matching type signature for left hand side ldom R a
-- it could belong to any of: ldom R

-- New error has position information.
-- error: [Syntax.AmbiguousFunClauses]
-- More than one matching type signature for left hand side ldom R a
-- it could belong to any of:
-- ldom (at Issue1499.agda:6.1-5)
-- R (at Issue1499.agda:4.1-2)
