open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)

test : (x : Nat) (y : Fin x) {z : Nat} → x ≡ suc z → Set
test .(suc z) y {z} refl = Nat

-- Telescope: (z : Nat) (y : Fin (suc z))
--  agda rep: ("z" , Nat) ("y" , Fin (suc @0))
-- Patterns:  test .(suc @1) @0 @1 refl = ?

macro
  testDef : Term → TC _
  testDef goal = do
    d  ← getDefinition (quote test)
    `d ← quoteTC d
    unify `d goal

foo : Definition
foo = testDef

fooTest : foo ≡ function
                  (clause
                   (("z" , arg (arg-info hidden relevant) (def (quote Nat) [])) ∷
                    ("y" ,
                     arg (arg-info visible relevant)
                     (def (quote Fin)
                      (arg (arg-info visible relevant)
                       (con (quote Nat.suc)
                        (arg (arg-info visible relevant) (var 0 []) ∷ []))
                       ∷ [])))
                    ∷ [])
                   (arg (arg-info visible relevant)
                    (dot
                     (con (quote Nat.suc)
                      (arg (arg-info visible relevant) (var 1 []) ∷ [])))
                    ∷
                    arg (arg-info visible relevant) (var 0) ∷
                    arg (arg-info hidden relevant) (var 1) ∷
                    arg (arg-info visible relevant) (con (quote refl) []) ∷ [])
                   (def (quote Nat) [])
                   ∷ [])
fooTest = refl

defBar : (name : Name) → TC _
defBar x = do
  function cls ← returnTC foo
    where _ → typeError []
  defineFun x cls

bar : (x : Nat) (y : Fin x) {z : Nat} → x ≡ suc z → Set
unquoteDef bar = defBar bar
