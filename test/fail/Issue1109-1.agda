postulate
  A   : Set
  x   : A
  f   : A → A → A
  _●_ : A → A → A

infix -666 _●_

syntax f x y = x ○ y

doesn't-parse : A
doesn't-parse = x ○ x ● x

-- The code parses if -666 is replaced by -665 or -667… The number
-- -666 is used in the definition of Agda.Syntax.Fixity.noFixity. The
-- fix of Issue 1109 made this implementation detail/hack visible to
-- users. Was this intended?
