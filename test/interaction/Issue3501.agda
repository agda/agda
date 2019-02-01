open import Agda.Builtin.Bool

f : Bool → Bool
f x =
  let id : Bool → Bool
      id b = {!!}
  in id x
