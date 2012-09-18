-- {-# OPTIONS -v tc.polarity:15 -v tc.pos:0 #-}
module Issue148 where

data I : Set where
  i : I

F : I → Set → Set
F i A = A

data T (p : I) : Set where
  t₁ :      T p  → T p
  t₂ : F p (T p) → T p

fold : ((x : T i) → T i) → T i → T i
fold f (t₁ x) = f (fold f x)
fold f (t₂ x) = f (fold f x)

data E : T i → Set where
  e : ∀ x → E x

postulate
  t₂′ : ∀ {p} → F p (T p) → T p

foo : (x : T i) → E (fold t₂ x)
foo x with x
foo x | x′ = e (fold t₂ x′)
