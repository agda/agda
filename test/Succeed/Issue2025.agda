-- Care needs to be taken to distinguish between instance solutions with and
-- without leftover constraints.
module _ where

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

postulate
  Functor : (Set → Set) → Set₁
  fmap : ∀ {F} {{_ : Functor F}} {A B} → (A → B) → F A → F B
  List : Set → Set
  map : ∀ {A B} → (A → B) → List A → List B
  Term : Set
  Arg : Set → Set

  instance FunArg : Functor Arg

postulate
  SafeTerm  : Set
  safe-term : SafeTerm → Term
  DeBruijn : Set → Set₁
  weaken : ∀ {A} {{_ : DeBruijn A}} → A → A
  instance
    DBTerm : DeBruijn Term
    DBArg : ∀ {A} {{_ : DeBruijn A}} → DeBruijn (Arg A)

toArgs : List (Arg SafeTerm) → List (Arg Term)
toArgs = map (weaken ∘ fmap safe-term)

