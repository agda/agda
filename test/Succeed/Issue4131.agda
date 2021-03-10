
postulate
  A : Set

works : Set
works = let B : {X : Set} → Set
            B = let _ = Set in A
        in A

fails : Set
fails = let B : {X : Set} → Set
            B = A   -- Set !=< {X : Set} → Set
        in A
