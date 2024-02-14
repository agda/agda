
postulate A : Set

module M where
  postulate a : A

x : A
x = {! M.a !} -- No solution found

open M

y : A
y = {! M.a !} -- works
