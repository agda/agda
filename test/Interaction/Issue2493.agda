-- Andreas, 2017-03-10, issue #2493, reported by nad
-- {-# OPTIONS -v tc.meta.assign:10 -v tc.size:90 -v tc:30 #-}

A : Set
A = {!!}

P : A → Set
P = {!λ _ → ?!}  -- give

-- Giving this made Agda loop as it solved ?0 := A.
-- Solution: don't assign metas during CheckInternal!
