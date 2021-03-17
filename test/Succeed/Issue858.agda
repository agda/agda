module Issue858 where

module _ (A B : Set) (recompute : .B → .{{A}} → B) where

  _$_ : .(A → B) → .A → B
  f $ x with .{f} | .(f x) | .{{x}}
  ... | y = recompute y

module _ (A B : Set) (recompute : ..B → ..{{A}} → B) where

  _$'_ : ..(A → B) → ..A → B
  f $' x with ..{f} | ..(f x) | ..{{x}}
  ... | y = recompute y
