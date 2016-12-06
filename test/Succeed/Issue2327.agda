
data Unit : Set where
  unit : Unit

mutual

  data D : Unit → Set where
    c : (x : Unit) → F x x → D x

  F : Unit → Unit → Set
  F unit x = D x

Works : (x : Unit) → D x → Set₁
Works .x (c x p) with x
Works .x (c x p) | _  = Set

Fails : (x : Unit) → D x → Set₁
Fails y = Fails′ y
  where
  Fails′ : (x : Unit) → D x → Set₁
  Fails′ .x (c x p) with x
  Fails′ .x (c x p) | _  = Set
