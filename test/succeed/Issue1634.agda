-- Andreas, 2015-08-27, issue reported by Jesper Cockx

-- {-# OPTIONS -v tc.lhs:10 #-}
-- {-# OPTIONS -v tc:10 #-}
-- {-# OPTIONS -v tc.lhs.imp:100 #-}

data Bool : Set where true false : Bool

T : Set → Bool → Set
T A true = {x : A} → A
T A false = (x : A) → A

test : (A : Set) (b : Bool) → T A b
test A true {x} = x
test A false x = x
