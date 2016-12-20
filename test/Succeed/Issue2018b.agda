
module _ {A : Set} where

postulate B : Set

postulate
  H : {A : Set} → Set

test-H : Set
test-H = H {A = B}

record R {A : Set} : Set where
  constructor rc
  field f : A

test-R : Set
test-R = R {A = B}

test-f : ∀ B → R {A = B} → B
test-f B = R.f {A = B}

module N {A : Set} where

module test-N = N {A = B}
