postulate
  A   : Set
  x   : A
  f   : A → A → A
  _●_ : A → A → A

infix -667 _●_

syntax f x y = x ○ y

doesn't-parse : A
doesn't-parse = x ○ x ● x
