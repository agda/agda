-- Andreas, 2024-08-29
-- Sections not allowed in idiom brackets

postulate
  F     : Set → Set
  pure  : ∀ {A} → A → F A
  _<*>_ : ∀ {A B} → F (A → B) → F A → F B

postulate
  A     : Set
  _⊕_   : A → A → A
  a b c : F A
  f     : A → A → A

infixl 5 _⊕_

-- Various experiments:

_ = (| f |)
_ = (| f a |)
_ = (| f a b |)
_ = (| λ x y → f x y |)  -- same as (| f |)
-- _ = (| λ x → f a x |) -- (F A) !=< A
-- _ = (| (f a) b |) -- (F A) !=< A

_ = (| (| a ⊕ b |) ⊕ c |)  -- Accepted
-- _ = (| a ⊕ b ⊕ c |)  -- Ill-typed

accepted0 = (| _⊕_ |)
accepted2 = (| a ⊕ b |)

-- Trigger error:

-- rejected1 = (| λ x → a ⊕ x |)
-- rejected1 = (|  a ⊕_ |)
rejected1 = (|  _⊕ b |)

-- Error: Naked sections are not allowed in idiom brackets
