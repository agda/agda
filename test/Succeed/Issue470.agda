module Issue470 where

data Bool : Set where
  true false : Bool

_and_ : Bool → Bool → Bool
true  and x = x
false and x = false

infixr 5 _∷_

data Foo : Bool → Set where
  []  : Foo true
  _∷_ : ∀ {b} (x : Bool) → Foo b → Foo (x and b)

Baz : Bool → Set
Baz true = Bool
Baz false = Foo false

data Bar : ∀ {b} → Foo b → Set where
  []  : Bar []
  _∷_ : ∀ {b} {foo : Foo b} {x} (g : Baz x) → (bar : Bar foo) → Bar (x ∷ foo)

foo : Foo false
foo = false ∷ true ∷ []

bar : Bar foo
bar = (false ∷ []) ∷ false ∷ [] -- ← is yellow

{-
_59 := _55 ∷ false ∷ [] [blocked by problem 75]
[75] ["apply" (_53 ∷ true ∷ [])] == ["apply" (false ∷ true ∷ [])] : Foo
(_53 and (true and true)) → Set [blocked by problem 76]
[76] (_53 and (true and true)) = false : Bool
_54 := false ∷ [] :? Baz _53
-}
