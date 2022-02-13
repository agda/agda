-- Andreas, 2017-10-04, issue #2752, report and test case by nad
--
-- Problem was: instance does not distribute into mutual blocks.

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.List
open import Agda.Builtin.Size

mutual

  data Rose (i : Size) (A : Set) : Set where
    node : List (Rose′ i A) → Rose i A

  data Rose′ (i : Size) (A : Set) : Set where
    delay : {j : Size< i} → Rose j A → Rose′ i A

record Map (F : Set → Set) : Set₁ where
  field
    map : {A B : Set} → (A → B) → F A → F B

open Map ⦃ … ⦄ public

instance

  Map-List : Map List
  Map.map Map-List = λ where
    f []       → []
    f (x ∷ xs) → f x ∷ map f xs

instance

  mutual

    Map-Rose : ∀ {i} → Map (Rose i)
    Map.map Map-Rose f (node xs) = node (map (map f) xs)

    Map-Rose′ : ∀ {i} → Map (Rose′ i)
    Map.map Map-Rose′ f (delay t) = delay (map f t)

-- Was: unresolved instance arguments.

-- Should succeed.
