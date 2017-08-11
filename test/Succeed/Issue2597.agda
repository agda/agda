
postulate A : Set

record Overlap : Set where
  constructor mk
  field overlap {{a}} : A

record NoOverlap : Set where
  constructor mk
  field {{a}} : A

ok : A → NoOverlap
ok a = mk {{a}}

bad : A → Overlap
bad a = mk {{a}}
-- Function does not accept argument {{a}}
-- when checking that {{a}} is a valid argument to a function of type
-- {{a = a₁ : A}} → Overlap
