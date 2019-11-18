
open import Issue4037.Import using (Id; _≟_)

data Expr : Set where
  var : Id → Expr

convert : Id → Expr → Expr
convert id (var x) with id ≟ x
...                 |   p      = {!p!}
