postulate A : Set
postulate B : A → Set
variable a : A

foo : B a → Set
foo x = {!a!} -- WAS: C-c C-c here reports "Not a variable: a"

-- SHOULD instead introduce the hidden argument {a}

{- C-c C-e reports
a : A  (not in scope)
x : B a
-}
