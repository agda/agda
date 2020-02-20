-- Andreas, 2019-08-19, issue #4007 reported by nad

-- The scope checker was not run in the TCEnv of the interaction meta.
-- Thus, the extended lambda was not inheriting the IsAbstract from
-- the AbstractMode of the meta, leading to checking the
-- extended lambda in the wrong ConcreteMode.

-- {-# OPTIONS -v interaction.give:20 #-}
-- {-# OPTIONS -v scope.extendedLambda:10 #-}
-- {-# OPTIONS -v tc.term.exlam:20 #-}
-- -- {-# OPTIONS -v tc.decl:10 #-}
-- {-# OPTIONS -v tc.interaction:20 #-}
-- {-# OPTIONS -v tc.decl.abstract:25 #-}
-- {-# OPTIONS -v tc.meta.check:20 #-}
-- {-# OPTIONS -v tc.meta.new:50 #-}

abstract

  data D : Set where
    c : D

  works : D → D
  works = λ { c → c }

  test : D → D
  test = {!λ { c → c }!} -- give

-- Giving should succeed.
