-- Andreas, 2019-02-23, issue #3586, reported by mcoblenz shrunk by G. Allais
-- WAS: Internal error in ConcreteToAbstract.

-- {-# OPTIONS -v scope.pat:60 #-}

infixl 5 ^_

data D : Set where
  ^_ : D → D

postulate
  _^_ : D → D → D

foo : D → Set
foo x@(y ^ z) = D

-- The term "y ^ z" is parsed as operator pattern (_^_ y z)
-- with _^_ being a variable name.
-- That is nonsense the scope checker did not expect and crashed.
-- Now, we report instead:
--
--   y ^ z is not a valid pattern
