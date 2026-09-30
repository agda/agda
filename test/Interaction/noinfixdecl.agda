{-# OPTIONS -Wall #-}

module noinfixdecl where

-- warning acts on data constructors
data #2 : Set where
  one  : #2
  two  : #2
  neg_ : #2 → #2

-- warning acts on definitions
infixl 3 _⊓_
_⊔_ : #2 → #2 → #2
_⊓_ : #2 → #2 → #2

one     ⊔ n = n
two     ⊔ n = two
(neg v) ⊔ n = neg (v ⊓ neg n)

one     ⊓ n = one
two     ⊓ n = n
(neg m) ⊓ n = neg (m ⊔ (neg n))

-- warning acts on postulates
postulate _≤_ : #2 → #2 → Set

-- warning does not act on 'closed' mixfix definitions
postulate [_] : #2 → Set
