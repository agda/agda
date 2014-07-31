
open import Common.Prelude
open import Common.Reflect

data D (A : Set) : Nat → Set where
  d : ∀ {n} → A → D A n

pattern hArg a = arg (arginfo hidden relevant) a
pattern vArg a = arg (arginfo visible relevant) a

term : Term
term = con (quote d) (hArg (def (quote Nat) []) ∷ vArg (con (quote zero) []) ∷ [])

-- There was a bug where extra implicit arguments were inserted for the parameters, resulting in
-- the unquoted value 'd {_} {Nat} zero' instead of 'd {Nat} zero'.
value : D Nat zero
value = unquote term
