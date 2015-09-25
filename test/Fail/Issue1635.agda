-- {-# OPTIONS -v scope:10 -v scope.inverse:100 #-}

open import Common.Equality
open import A.Issue1635 Set

test : ∀ x → x ≡ foo
test x = refl

-- ERROR:
-- x != .#A.Issue1635-225351734.foo of type Foo
-- when checking that the expression refl has type x ≡ foo

-- SLIGHTLY BETTER:
-- x != .A.Issue1635.Foo.foo of type Foo
-- when checking that the expression refl has type x ≡ foo

-- WANT: x != foo ...
