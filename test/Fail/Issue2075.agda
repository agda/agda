data Unit : Set where
  unit : Unit

F : Unit → Set₁
F {x = unit} = Set
