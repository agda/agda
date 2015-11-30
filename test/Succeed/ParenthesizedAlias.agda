-- Andreas, 2015-11-28
-- Aliases in parentheses should also parse.

-- Parenthesized aliases are accepted in lets.

-- With type annotation, parenthesized aliases are accepted in wheres.

id0 : {A : Set} → A → A
id0 {A} x = let z = y in z
  where
    y : A
    y = x

id1 : {A : Set} → A → A
id1 {A} x = let (z) = y in z
  where
    y : A
    (y) = x

id2 : {A : Set} → A → A
id2 {A} x = let ((z)) = y in z
  where
    y : A
    ((y)) = x

works0 : {A : Set} → A → A
works0 x = let z = y in z
  where
    y = x

-- Without type annotation, parenthesized aliases should also be accepted in wheres.

-- Should work:
test1 : {A : Set} → A → A
test1 x = let (z) = y in z
  where
    (y) = x

-- Should work:
test2 : {A : Set} → A → A
test2 x = let ((z)) = y in z
  where
    ((y)) = x
