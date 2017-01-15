-- Andreas, 2016-12-30, issue #1886, reported by nad

-- {-# OPTIONS -v tc.data:40 -v scope.data.def:40 -v tc.decl:10 #-}

data D (X : Set) : Set

data D (X : Set Set) where
