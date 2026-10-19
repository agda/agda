-- Andreas, 2016-12-20, issue #2347, reported by m0davis
-- Case splitting in extended lambda with instance argument
-- was printed wrongly

-- {-# OPTIONS -v interaction.case:100 #-}
-- {-# OPTIONS -v reify:100 #-}
-- {-# OPTIONS -v reify.clause:100 #-}
-- {-# OPTIONS -v extendedlambda:100 #-}
-- {-# OPTIONS -v tc.term.extlam:100 #-}


data ⊥ : Set where

works : ⊥ → Set
works = λ {x → {!x!}}

works1 : { _ : Set } → ⊥ → Set
works1 = λ {x → {!x!}}

test : ⦃ _ : Set ⦄ → ⊥ → Set
test = λ {x → {!x!}}

-- Case splitting on x should succeed in each case
