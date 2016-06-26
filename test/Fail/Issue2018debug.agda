-- Andreas, 2016-06-21 fixed context for a debug message

{-# OPTIONS -v tc.section:10 #-} -- KEEP! to print debug message

module _ {A : Set} where

postulate B : Set

module M {A : Set} where

-- Intentional crash:

fail : Set
fail = Set

-- Expected debug printout:

-- checking section Issue2018debug {A = A₁ : Set}
--     actual tele: {A : Set}
-- checking section M {A = A₁ : Set}
--     actual tele: {A : Set} {A₁ : Set}
--
-- The last "actual tele" hints to a problem: Agda has renamed the second parameter!
