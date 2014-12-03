-- Andreas, 2014-12-03 Issue reported by Fabien Renaud

postulate A : Set

f : A → A
g : A → A

f x = g x

ok : A → A
ok x = x

g x = f x

-- Only `f` and `g` should be colored red, not `ok`.

