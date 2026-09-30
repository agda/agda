record R (A : Set) : Set where
  field
    f : A → A

open R {{...}}

test : {A : Set} → R A
f {{test}} = {!!}
