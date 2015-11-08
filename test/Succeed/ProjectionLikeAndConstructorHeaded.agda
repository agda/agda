{- Constructor-headedness and projection-likeness don't play well
   together. Unless they are kept apart or their differences can
   be reconciled this example will leave unsolved metas. The problem
   is that invoking constructor-headedness on a projection-like
   the dropped arguments won't be checked (or rather, the type of
   the eliminatee, which is where the dropped arguments live, isn't
   checked).
-}
module ProjectionLikeAndConstructorHeaded where

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

data ⊥ : Set where
record ⊤ : Set where

data Dec (P : Set) : Set where
  yes : ( p : P) → Dec P
  no  : (¬p : P → ⊥) → Dec P

data Bool : Set where
  false true : Bool

T : Bool → Set
T true  = ⊤
T false = ⊥

⌊_⌋ : ∀ {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

True : ∀ {P : Set} → Dec P → Set
True Q = T ⌊ Q ⌋

toWitness : ∀ {P : Set} {Q : Dec P} → True Q → P
toWitness {Q = yes p} _  = p
toWitness {Q = no  _} ()

postulate
  _≤_    : ℕ → ℕ → Set
  fromℕ≤ : ∀ {m n} → m ≤ n → Fin n
  _≤?_   : ∀ n m → Dec (n ≤ m)

#_ : ∀ m {n} {m<n : True (m ≤? n)} → Fin n
#_ m {n} {m<n = m<n} = fromℕ≤ {_} {n} (toWitness {_ ≤ n} {_} m<n)
