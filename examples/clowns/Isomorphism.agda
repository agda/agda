
module Isomorphism where

  import Sets
  open Sets

  infix 20 _≅_

  data _≅_ (A B : Set) : Set where
    iso : (i : A -> B)(j : B -> A) ->
	  (forall x -> j (i x) == x) ->
	  (forall y -> i (j y) == y) ->
	  A ≅ B

  refl-≅ : (A : Set) -> A ≅ A
  refl-≅ A = iso id id (\x -> refl) (\x -> refl)

  iso[×] : {A₁ A₂ B₁ B₂ : Set} -> A₁ ≅ A₂ -> B₁ ≅ B₂ -> A₁ [×] B₁ ≅ A₂ [×] B₂
  iso[×] (iso a₁₂ a₂₁ p₁₁ p₂₂) (iso b₁₂ b₂₁ q₁₁ q₂₂) =
    iso ab₁₂ ab₂₁ pq₁₁ pq₂₂ where

    ab₁₂ = a₁₂ <×> b₁₂
    ab₂₁ = a₂₁ <×> b₂₁

    pq₂₂ : (z : _ [×] _) -> ab₁₂ (ab₂₁ z) == z
    pq₂₂ < x , y > =
      subst (\ ∙ -> < ∙ , b₁₂ (b₂₁ y) > == < x , y >) (p₂₂ x)
      $ cong < x ,∙> (q₂₂ y)

    pq₁₁ : (z : _ [×] _) -> ab₂₁ (ab₁₂ z) == z
    pq₁₁ < x , y > =
      subst (\ ∙ -> < ∙ , b₂₁ (b₁₂ y) > == < x , y >) (p₁₁ x)
      $ cong < x ,∙> (q₁₁ y)

  iso[+] : {A₁ A₂ B₁ B₂ : Set} -> A₁ ≅ A₂ -> B₁ ≅ B₂ -> A₁ [+] B₁ ≅ A₂ [+] B₂
  iso[+] (iso a₁₂ a₂₁ p₁₁ p₂₂) (iso b₁₂ b₂₁ q₁₁ q₂₂) =
    iso ab₁₂ ab₂₁ pq₁₁ pq₂₂ where

    ab₁₂ = a₁₂ <+> b₁₂
    ab₂₁ = a₂₁ <+> b₂₁

    pq₂₂ : (z : _ [+] _) -> ab₁₂ (ab₂₁ z) == z
    pq₂₂ (inl x) = cong inl (p₂₂ x)
    pq₂₂ (inr y) = cong inr (q₂₂ y)

    pq₁₁ : (z : _ [+] _) -> ab₂₁ (ab₁₂ z) == z
    pq₁₁ (inl x) = cong inl (p₁₁ x)
    pq₁₁ (inr y) = cong inr (q₁₁ y)

