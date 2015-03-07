data D : Set₁ where
  ⟨_⟩_ : Set → Set → D

Test : D → Set
Test ((⟨_⟩ X) _) = X
