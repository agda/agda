{-# OPTIONS --allow-unsolved-metas #-}
postulate
  Foo : Set

record BaseT : Set₁ where
  field f : Foo

record ParamT (p : Foo) : Set₁ where
  field f : Foo

instance
  postulate asBaseT : ∀ {p} {{_ : ParamT p}} → BaseT
--  BaseT.f (asBaseT p) = ParamT.f p

data Bar : Set where
  o : Bar

data Baz {{_ : BaseT}} : Bar → Set where
  t1 : Baz o
  t2 : Baz o → Baz o
  t3 : Baz o → Baz o → Baz o
  t4 : Baz o → Baz o → Baz o → Baz o
