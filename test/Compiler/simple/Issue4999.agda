
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Char renaming (primCharEquality to _==ᶜ_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.String renaming (primStringAppend to _++_)
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

variable
  A B C : Set

map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

<?> = '\xFFFD'

fromCount : Nat → Nat → List Nat
fromCount 0 _ = []
fromCount (suc n) a = a ∷ fromCount n (suc a)

fromTo : Nat → Nat → List Nat
fromTo a b = fromCount (suc b - a) a

isReplaced : Nat → Bool
isReplaced n = primNatToChar n ==ᶜ <?>

and : List Bool → Bool
and []           = true
and (false ∷ _)  = false
and (true  ∷ xs) = and xs

all : (A → Bool) → List A → Bool
all p xs = and (map p xs)

not : Bool → Bool
not false = true
not true  = false

_∘_ : (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

postulate
  putStrLn : String → IO ⊤
  _>>_ : IO A → IO B → IO B

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC _>>_ = \ _ _ -> (>>) #-}

assert : String → Bool → IO ⊤
assert s true  = putStrLn (s ++ " PASSED")
assert s false = putStrLn (s ++ " FAILED")

main : IO ⊤
main = do
  assert "before surrogates" (all (not ∘ isReplaced) (fromTo 0xD780 0xD7FF))
  assert "surrogate range  " (all isReplaced (fromTo 0xD800 0xDFFF))
  assert "after surrogates " (all (not ∘ isReplaced) (fromTo 0xE000 0xE07F))
