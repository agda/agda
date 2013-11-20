
data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : Dec A

record ⊤ : Set where constructor tt

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

subst : ∀ {A}(P : A → Set){x y} → x ≡ y → P x → P y
subst P refl px = px

cong : ∀ {A B}(f : A → B){x y} → x ≡ y → f x ≡ f y
cong f refl = refl

postulate _≟_ : (n n' : ⊤) → Dec (n ≡ n')

record _×_ A B : Set where
  constructor _,_
  field proj₁ : A
        proj₂ : B

open _×_

data Maybe : Set where
  nothing : Maybe

data Blah (a : Maybe × ⊤) : Set where
  blah  : {b : Maybe × ⊤} → Blah b → Blah a

update : {A : Set} → ⊤ → A → A
update n m with n ≟ n
update n m | yes p  = m
update n m | no     = m

lem-upd : ∀ {A} n (m : A) → update n m ≡ m
lem-upd n m with n ≟ n
... | yes p = refl
... | no    = refl

bug : {x : Maybe × ⊤} → proj₁ x ≡ nothing → Blah x
bug ia = blah (bug (subst {⊤}
                      (λ _ → proj₁ {B = ⊤}
                                   (update tt (nothing , tt)) ≡ nothing)
                   refl (cong proj₁ (lem-upd _ _))))