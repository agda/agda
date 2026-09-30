postulate P : Set -> Set

test : (B : Set) -> P B -> P B
test = λ p p -> {!!}

postulate A : Set

test₂ : Set → A
test₂ A = {!!}
