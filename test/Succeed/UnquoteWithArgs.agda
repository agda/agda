
module _ where

open import Common.Prelude
open import Common.Reflection

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x

id : ∀ {a} {A : Set a} → A → A
id x = x

first : Tactic
first = give (def (quote const) [])

second : Tactic
second = give (def (quote const) (arg (argInfo visible relevant) (def (quote id) []) ∷ []))

number : Nat
number = unquote first 6 false

boolean : Bool
boolean = unquote second 5 true
