open import Agda.Builtin.Equality

postulate
  A : Set
  eq : (a b : A) → a ≡ b

case_of_ : {A B : Set} → A → (A → B) → B
case x of f = f x

foo : (a b c d : A) → a ≡ d
foo a b c d = bar
  where
  bar : a ≡ d
  bar =
    case eq a b of λ where
      refl →
        case eq b c of λ where
          refl →
            case eq c d of λ where
              refl →
                {!!}
