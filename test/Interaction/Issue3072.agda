
postulate
  S : Set
  id : S
  comp : S → S → S

module C where
  _∘_ = comp

postulate
  R : (S → S) → Set
  T : R (C._∘ id) → R (id C.∘_) → Set

t : Set
t = T {!!} {!!}
