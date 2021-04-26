module _ where

record Foo : Set₂ where
  field foo : Set₁
record Bar (f : Foo) : Set₂ where
  field bar : Set₁
resize : ∀ f g → Bar f → Bar g
resize f g b = record { bar = Bar.bar b }

resize' : ∀ f g → Bar f → Bar g
resize' f g b = {!resize f g b!}
