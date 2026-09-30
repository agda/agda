-- Andreas, 2015-07-16
-- For printing lambda-bound names, name _ should behave as no name.

-- {-# OPTIONS -v tc.term.lambda:60 #-}

module _ where

Test = (A : Set) {A : Set} → A → A

works : Test
works = λ C x → {!!}

-- the goal should be displayed as ?0 : .A

g : Test
g = λ C {_} x → {!!}

-- the goal should be displayed as ?1 : .A
-- not ?1 : _ or ?1 : A

h : Test
h = λ C {_} → λ x → {!!}

-- the goal should be displayed as ?1 : .A
-- not ?1 : _ or ?1 : A
