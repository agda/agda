
open import Agda.Builtin.Reflection
open import Agda.Builtin.Equality
open import Agda.Builtin.Int
open import Agda.Builtin.String
open import Common.Prelude

getFixity = primQNameFixity

infixl -1729 _to_
_to_ : Set → Set → Set
A to B = A → B

data Check : Set₁ where
  equal : {A : Set} (x y : A) → x ≡ y → Check

pattern _==_ x y = equal x y refl

check-cons = getFixity (quote _∷_)  == fixity right-assoc (related 5.0)
check-to   = getFixity (quote _to_) == fixity left-assoc  (related -1729.0)
check-eq   = getFixity (quote _≡_)  == fixity non-assoc   (related 4.0)
check-list = getFixity (quote List) == fixity non-assoc   unrelated

showAssoc : Associativity → String
showAssoc left-assoc  = "infixl"
showAssoc right-assoc = "infixr"
showAssoc non-assoc   = "infix"

showFixity : Fixity → String
showFixity (fixity a unrelated)   = "(no fixity)"
showFixity (fixity a (related p)) = showAssoc a +S+ " " +S+ floatToString p

showFix : Name → String
showFix x = showFixity (getFixity x)

main : IO Unit
main = putStrLn (showFix (quote _∷_))  >>= λ _ →
       putStrLn (showFix (quote _to_)) >>= λ _ →
       putStrLn (showFix (quote _≡_))  >>= λ _ →
       putStrLn (showFix (quote List)) >>= λ _ →
       return unit
