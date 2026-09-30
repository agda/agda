
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

postulate
  P : {X : Set} → X → Set
  H : Set
  R : H → Set
  x : H
  y : R x
  help : (f : H) (p : R f) → P {X = Σ H R} (f , p)

record Category : Set₁ where
  field
    Hom : Set
    id : Hom
    comp : Hom → Hom
    neut-l : P (comp id)
    neut-r : Hom

slice : Category
slice = λ where
  .Category.Hom → Σ H R
  .Category.id → (x , y)
  .Category.comp (f , p) → (f , p)
  .Category.neut-l → help x _
  .Category.neut-r → {!!}
