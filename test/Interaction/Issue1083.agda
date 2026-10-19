-- Andreas, 2013-04-06
-- Interaction point buried in postponed type checking problem

module Issue1083 where

data Bool : Set where true false : Bool

T : Bool → Set
T true  = Bool → Bool
T false = Bool → Bool

postulate
  f : {x : Bool} → T x

test : (x : Bool) → T x
test true = f {!!}
test false = {!!}

-- Constraints show: _10 := (_ : T _x_9) ? : Bool
-- So there is a question mark which has never been seen by the type checker.
-- It is buried in a postponed type-checking problem.

-- Interaction points should probably be created by the scope checker,
-- and then hooked up to meta variables by the type checker.

-- This is how it works now.
