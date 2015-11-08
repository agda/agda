-- There was a bug with module applications in let.
module Issue34 where

module A (X : Set) where
  postulate A : Set

T : (X : Set) -> let open A X in A -> Set
T X _ = X

record B (X : Set) : Set where
  open A X
  field f : A

postulate
  foo : (X : Set)(b : B X) ->
        let open A X
            open B b in
        A -> Set
