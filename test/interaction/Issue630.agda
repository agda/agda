module Issue630 where

Test = (A : Set) → A → A

g : Test
g = λ _ x → {!!}

-- the goal should be displayed as ?1 : A
-- not ?1 : _
