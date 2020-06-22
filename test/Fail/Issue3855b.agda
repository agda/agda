-- Andreas, 2019-06-25, issue #3855 reported by nad
-- Constraint solver needs to respect erasure.

module _
  (_≡_ : {A : Set₁} → A → A → Set)
  (refl : {A : Set₁} (x : A) → x ≡ x)
  where

-- rejected : (@0 A : Set) → A ≡ A
-- rejected A = refl A

should-also-be-rejected : (@0 A : Set) → A ≡ A
should-also-be-rejected A = refl _
