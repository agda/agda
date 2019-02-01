record R : Set₁ where
  field
    ⟨_+_⟩ : Set

open R

-- Name parts coming from projections can not be used as part of the
-- defined name.

+ : Set → Set
+ A = A
