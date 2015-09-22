postulate
  A   : Set
  x   : A
  f   : A → A → A
  _●_ : A → A → A

infix 20 _●_

syntax f x y = x ○ y

doesn't-parse : A
doesn't-parse = x ○ x ● x

-- Default fixity for syntax is no longer -666, but 20 as for normal operators.
