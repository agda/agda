-- Andreas, 2014-01-09, extend parser of typed bindings to allow hiding

postulate
  _≡_   : ∀{A : Set} (a b : A) → Set
  List  : Set → Set
  _++_  : ∀{A : Set} (xs ys : List A) → List A
  assoc : ∀{A : Set} (xs {ys} {zs} : List A) → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
  assoc1 : ∀{A : Set} (xs {ys zs} : List A) → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
  test  : (xs {ys zs} _ us : Set) → Set
  test1 : .(xs {ys zs} _ us : Set) → Set
  test2 : ..(xs {ys zs} _ us : Set) → Set
