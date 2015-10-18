id : Set → Set
id A = A

F : Set → Set → Set
F _*_ = G
  where
  G : Set → Set
  G _*_ = id _*_

G : Set → Set → Set
G _*_ = λ _*_ → id _*_

H : Set → Set → Set
H = λ _*_ _*_ → id _*_
