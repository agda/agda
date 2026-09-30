
postulate
  M : Set → Set
  _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  _>>_  : ∀ {A B} → M A → M B → M B
  _<|>_ : ∀ {A} → M A → M A → M A

infixr 4 _>>=_ _>>_
infixr -100 _<|>_

expr : ∀ {A} → (A → M A) → (A → M A)
expr f a = do
  x ← {!f a!}
  y ← {!f x <|> f a!}
  {!f x <|> f y!}
  {!f x <|> f y!}
