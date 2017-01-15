-- Andreas, 2014-02-17, reported by pumpkingod

{-# OPTIONS --allow-unsolved-metas #-}

data Bool : Set where true false : Bool

-- Equality

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_  #-}

subst : ∀ {a p}{A : Set a}(P : A → Set p){x y : A} → x ≡ y → P x → P y
subst P refl t = t

cong : ∀ {a b}{A : Set a}{B : Set b}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {a}{A : Set a}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a}{A : Set a}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

infix  3 _∎
infixr 2 _≡⟨_⟩_
infix  1 begin_

data _IsRelatedTo_ (x y : Bool) : Set where
  relTo : (x≡y : x ≡ y) → x IsRelatedTo y

begin_ : ∀ {x y} → x IsRelatedTo y → x ≡ y
begin relTo x≡y = x≡y

_≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
_ ≡⟨ x≡y ⟩ relTo y≡z = relTo (trans x≡y y≡z)

_∎ : ∀ x → x IsRelatedTo x
_∎ _ = relTo refl

-- Test

proof : true ≡ true
proof =
  begin
    true
  ≡⟨ {!!} ⟩
    {!!} -- If you do C-c C-s, it will fill in the first and last boxes, but it will also fill this one in with an underscore!
  ≡⟨ {!!} ⟩
    {!true!}
  ∎

-- C-c C-s should only solve for ?0 and ?4, not for ?2.



-- Constraints are

-- ?0 := true
-- ?2 := _y_38
-- ?4 := true

-- Metas are
--
-- ?0 : Bool
-- ?1 : true ≡ _y_38
-- ?2 : Bool
-- ?3 : _y_38 ≡ true
-- ?4 : Bool
-- _y_38 : Bool  [ at /home/abel/tmp/Agda2/test/bugs/Issue1060.agda:23,5-24,12 ]
