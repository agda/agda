_∋_ : (A : Set) → A → A
A ∋ x = x

it : {A : Set} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

postulate DecidableEquality : Set → Set

record DecEq (A : Set) : Set where
  field _≟_ : DecidableEquality A

module M where
  postulate A : Set; _≟_ : DecidableEquality A

instance
  --DecEq-A : DecEq _
  DecEq-A = DecEq _ ∋ record {M}
    where putAnythingHere!! = Set

-- _ = DecEq A ∋ it where open M
