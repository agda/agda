-- Andreas, 2018-07-21, issue #3161
-- Insert space before brace if preceeded by `-`.
-- (Symmetric case was already fixed in #269).

data Pol : Set where
  + - : Pol

f : {x : Pol} → Set
f {x} = {!x!}  -- Split on x here
