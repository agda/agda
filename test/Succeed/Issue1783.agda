-- Andreas, 2016-01-19, issue raised by Twey
-- {-# OPTIONS -v 10 #-}

{-# OPTIONS --allow-unsolved-metas #-}

Rel : Set → Set₁
Rel A = A → A → Set

record Category : Set₁ where
  field
    Obj : Set
    _⇒_ : Rel Obj -- unfolding the definition of Rel removes the error

record Product (C : Category) (A B : Category.Obj C) : Set where
  field
    A×B : Category.Obj C

postulate
  anything : ∀{a}{A : Set a} → A

trivial : ∀ {C} → Category.Obj C → Set
trivial _ = anything

map-obj : ∀ {P : _} → trivial (Product.A×B P) -- Note: hole _ cannot be filled
map-obj = anything

{- Error thrown during printing open metas:
piApply
  t    = Rel _24   Def Issue1783.Rel [Apply []r(MetaV (MetaId 24) [])]}
  args = @0        [[]r{Var 0 []}]
An internal error has occurred. Please report this as a bug.
Location of the error: src/full/Agda/TypeChecking/Substitute.hs:382
-}
