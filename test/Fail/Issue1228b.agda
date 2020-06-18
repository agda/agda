
open import Common.Prelude hiding (tt)
open import Common.Reflection
open import Common.Equality
open import Agda.Builtin.Sigma

tt : ⊤
tt = record{}

NoConf : Nat → Nat → Set
NoConf zero zero = ⊤
NoConf zero (suc n) = ⊥
NoConf (suc m) zero = ⊥
NoConf (suc m) (suc n) = m ≡ n

pattern `Nat = def (quote Nat) []

infixr 0 Π
syntax Π x a b = [ x ∈ a ]→ b
Π : String → Type → Type → Type
Π x a b = pi (vArg a) (abs x b)

-- noConf : (m n : ℕ) → m ≡ n → NoConfusion-ℕ m n
-- noConf zero .zero refl = tt
-- noConf (suc m) .(suc m) refl = refl

noConf : FunDef
noConf = funDef
  ([ "A" ∈ `Nat ]→ [ "B" ∈ `Nat ]→
   [ "C" ∈ def (quote _≡_) (vArg (var 1 []) ∷ vArg (var 0 []) ∷ []) ]→
   def (quote NoConf) (vArg (var 2 []) ∷ vArg (var 1 []) ∷ []))
  ( clause []
           (vArg (con (quote zero) []) ∷ vArg (dot unknown) ∷ vArg (con (quote refl) []) ∷ [])
           (def (quote tt) [])
  ∷ clause (("m" , vArg unknown) ∷ [])
           (vArg (con (quote suc) (vArg (var 0) ∷ [])) ∷ vArg (dot unknown) ∷ vArg (con (quote refl) []) ∷ [])
           (def (quote refl) [])
  ∷ [])

unquoteDecl test = define (vArg test) noConf
