module Issue2858-Fresh {A : Set} (_#_ : A → A → Set) where

  interleaved mutual

    data Fresh : Set
    data IsFresh (a : A) : Fresh → Set

    -- nil is a fresh list
    constructor
      []  : Fresh
      #[] : IsFresh a []

    -- cons is fresh as long as the new value is fresh
    constructor
      cons  : (x : A) (xs : Fresh) → IsFresh x xs → Fresh
      #cons : ∀ {x xs p} → a # x → IsFresh a xs → IsFresh a (cons x xs p)
