------------------------------------------------------------------------
-- Properties relating Any to various list functions
------------------------------------------------------------------------

module Data.List.Any.Properties where

open import Category.Monad
open import Data.Bool
open import Data.Bool.Properties
open import Data.Function
open import Data.List as List
open RawMonad List.monad
open import Data.List.Any as Any using (Any; here; there)
import Data.List.Equality as ListEq
open import Data.Product as Prod hiding (map)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Unary using (Pred) renaming (_⊆_ to _⋐_)
open import Relation.Binary
open import Relation.Binary.FunctionSetoid
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≗_; inspect; _with-≡_)

-- Functions can be shifted between the predicate and the list.

Any-map : ∀ {A B} {P : Pred B} {f : A → B} {xs} →
          Any (P ∘₀ f) xs → Any P (map f xs)
Any-map (here p)  = here p
Any-map (there p) = there $ Any-map p

map-Any : ∀ {A B} {P : Pred B} {f : A → B} {xs} →
          Any P (map f xs) → Any (P ∘₀ f) xs
map-Any {xs = []}     ()
map-Any {xs = x ∷ xs} (here p)  = here p
map-Any {xs = x ∷ xs} (there p) = there $ map-Any p

-- A variant of Any.map.

gmap : ∀ {A B} {P : A → Set} {Q : B → Set} {f : A → B} →
       P ⋐ Q ∘₀ f → Any P ⋐ Any Q ∘₀ map f
gmap g = Any-map ∘ Any.map g

-- Introduction and elimination rules for Any on _++_.

Any-++ˡ : ∀ {A} {P : Pred A} {xs ys} → Any P xs → Any P (xs ++ ys)
Any-++ˡ (here refl)  = here refl
Any-++ˡ (there x∈xs) = there (Any-++ˡ x∈xs)

Any-++ʳ : ∀ {A} {P : Pred A} xs {ys} → Any P ys → Any P (xs ++ ys)
Any-++ʳ []       p = p
Any-++ʳ (x ∷ xs) p = there (Any-++ʳ xs p)

++-Any : ∀ {A} {P : Pred A} xs {ys} →
         Any P (xs ++ ys) → Any P xs ⊎ Any P ys
++-Any []       p           = inj₂ p
++-Any (x ∷ xs) (here refl) = inj₁ (here refl)
++-Any (x ∷ xs) (there p)   = Sum.map there id (++-Any xs p)

-- Any and any are related via T.

Any-any : ∀ {A} (p : A → Bool) {xs} →
          Any (T ∘₀ p) xs → T (any p xs)
Any-any p (here  px)  = proj₂ T-∨ (inj₁ px)
Any-any p (there {x = x} pxs) with p x
... | true  = _
... | false = Any-any p pxs

any-Any : ∀ {A} (p : A → Bool) xs →
          T (any p xs) → Any (T ∘₀ p) xs
any-Any p []       ()
any-Any p (x ∷ xs) px∷xs with inspect (p x)
any-Any p (x ∷ xs) px∷xs | true  with-≡ eq = here (proj₂ T-≡ (PropEq.sym eq))
any-Any p (x ∷ xs) px∷xs | false with-≡ eq with p x
any-Any p (x ∷ xs) pxs   | false with-≡ PropEq.refl | .false =
  there (any-Any p xs pxs)

-- The following private parameterised modules are reexported from
-- ListMembership₁ and ListMembership₂ below.

private
 module ListMembership₁₁ (S : Setoid) where

  open Any.ListMembership S
  private
    open module S = Setoid S using (_≈_)
    open module L = ListEq.Equality S using ([]; _∷_)
    module LM = Any.ListMembership L.setoid

  -- Any is monotone.

  mono : ∀ {P xs ys} →
         _≈_ Respects P → xs ⊆ ys → Any P xs → Any P ys
  mono resp xs⊆ys pxs with find pxs
  ... | (x , x∈xs , px) = lose resp (xs⊆ys x∈xs) px

  -- _++_ is monotone.

  _++-mono_ : ∀ {xs₁ xs₂ ys₁ ys₂} →
              xs₁ ⊆ ys₁ → xs₂ ⊆ ys₂ → xs₁ ++ xs₂ ⊆ ys₁ ++ ys₂
  _++-mono_ {ys₁ = ys₁} xs₁⊆ys₁ xs₂⊆ys₂ =
    [ Any-++ˡ ∘ xs₁⊆ys₁ , Any-++ʳ ys₁ ∘ xs₂⊆ys₂ ]′ ∘ ++-Any _

  -- _++_ is idempotent.

  ++-idempotent : ∀ {xs} → xs ++ xs ⊆ xs
  ++-idempotent = [ id , id ]′ ∘ ++-Any _

  -- Introduction and elimination rules for Any/_∈_ on concat.

  Any-concat : ∀ {P xs xss} → _≈_ Respects P →
               Any P xs → xs ⟨ LM._∈_ ⟩₁ xss → Any P (concat xss)
  Any-concat {P} {xs} resp p (here {x = ys} eq) =
    Any-++ˡ $ lift-resp resp eq p
  Any-concat resp p (there {x = ys} xs∈xss) =
    Any-++ʳ ys (Any-concat resp p xs∈xss)

  ∈-concat : ∀ {x xs xss} →
             x ∈ xs → xs ⟨ LM._∈_ ⟩₁ xss → x ∈ concat xss
  ∈-concat = Any-concat ≈-resp-∈

  concat-Any : ∀ {P} xss →
               Any P (concat xss) →
               ∃ λ xs → Any P xs × (xs ⟨ LM._∈_ ⟩₁ xss)
  concat-Any []               ()
  concat-Any ([]       ∷ xss) x∈cxss         = Prod.map id (Prod.map id there)
                                               (concat-Any xss x∈cxss)
  concat-Any ((x ∷ xs) ∷ xss) (here refl)    = (x ∷ xs , here refl , here L.refl)
  concat-Any ((y ∷ xs) ∷ xss) (there x∈cxss) with concat-Any (xs ∷ xss) x∈cxss
  ... | (zs , x∈zs , here zs≈xs)   = (y ∷ zs , there x∈zs , here (S.refl ∷ zs≈xs))
  ... | (ys , x∈ys , there ys∈xss) = (ys     , x∈ys       , there ys∈xss)

  -- concat is monotone.

  concat-mono : ∀ {xss yss} →
                xss ⟨ LM._⊆_ ⟩₁ yss → concat xss ⊆ concat yss
  concat-mono {xss = xss} xss⊆yss x∈ with concat-Any xss x∈
  ... | (xs , x∈xs , xs∈xss) = ∈-concat x∈xs (xss⊆yss xs∈xss)

  -- any is monotone.

  any-mono : ∀ p → _≈_ Respects (T ∘₀ p) →
             ∀ {xs ys} → xs ⊆ ys → T (any p xs) → T (any p ys)
  any-mono p resp xs⊆ys = Any-any p ∘ mono resp xs⊆ys ∘ any-Any p _

 module ListMembership₂₁ (S₁ S₂ : Setoid) where

  private
    module S₂  = Setoid S₂
    module LM₁ = Any.ListMembership S₁
    module LM₂ = Any.ListMembership S₂

  -- Introduction and elimination rules for _∈_ on map.

  ∈-map : ∀ (f : S₁ ⟶ S₂) {x xs} →
          let open _⟶_ f in
          x ⟨ LM₁._∈_ ⟩₁ xs → fun x ⟨ LM₂._∈_ ⟩₁ map fun xs
  ∈-map f = gmap (_⟶_.pres f)

  map-∈ : ∀ {f fx xs} →
          fx ⟨ LM₂._∈_ ⟩₁ map f xs →
          ∃ λ x → (x ⟨ LM₁._∈_ ⟩₁ xs) × (fx ⟨ S₂._≈_ ⟩₁ f x)
  map-∈ fx∈ = LM₁.find (map-Any fx∈)

  -- map is monotone.

  map-mono : ∀ (f : S₁ ⟶ S₂) {xs ys} →
             let open _⟶_ f in
             xs ⟨ LM₁._⊆_ ⟩₁ ys → map fun xs ⟨ LM₂._⊆_ ⟩₁ map fun ys
  map-mono f xs⊆ys fx∈ with map-∈ fx∈
  ... | (x , x∈ , eq) = Any.map (S₂.trans eq) (∈-map f (xs⊆ys x∈))

 module ListMembership₂₂ (S₁ S₂ : Setoid) where

  private
    module S₂   = Setoid S₂
    module L₂   = ListEq.Equality S₂
    module ALM₁ = Any.ListMembership S₁
    module ALM₂ = Any.ListMembership S₂
    module LM₂  = ListMembership₁₁ S₂
    module LM₁₂ = ListMembership₂₁ S₁ L₂.setoid

  -- Introduction and elimination rules for Any/_∈_ on _>>=_.

  Any->>= : ∀ {P} → S₂._≈_ Respects P →
            ∀ (f : S₁ ⟶ L₂.setoid) {x xs} →
            let open _⟶_ f in
            x ⟨ ALM₁._∈_ ⟩₁ xs → Any P (fun x) → Any P (xs >>= fun)
  Any->>= resp f x∈xs y∈fx = LM₂.Any-concat resp y∈fx (LM₁₂.∈-map f x∈xs)

  ∈->>= : ∀ (f : S₁ ⟶ L₂.setoid) {x y xs} →
          let open _⟶_ f in
          x ⟨ ALM₁._∈_ ⟩₁ xs → y ⟨ ALM₂._∈_ ⟩₁ fun x →
          y ⟨ ALM₂._∈_ ⟩₁ (xs >>= fun)
  ∈->>= f = Any->>= ALM₂.≈-resp-∈ f

  >>=-Any : ∀ {P} → S₂._≈_ Respects P →
            ∀ (f : S₁ ⟶ L₂.setoid) xs →
            let open _⟶_ f in
            Any P (xs >>= fun) →
            ∃ λ x → (x ⟨ ALM₁._∈_ ⟩₁ xs) × Any P (fun x)
  >>=-Any resp f xs p
    with Prod.map id (Prod.map id LM₁₂.map-∈) $
           LM₂.concat-Any (map (_⟶_.fun f) xs) p
  >>=-Any resp f xs p | (fx , p′ , (x , x∈xs , eq)) =
    (x , x∈xs , ALM₂.lift-resp resp eq p′)

  >>=-∈ : ∀ (f : S₁ ⟶ L₂.setoid) {y} xs →
          let open _⟶_ f in
          y ⟨ ALM₂._∈_ ⟩₁ (xs >>= fun) →
          ∃ λ x → (x ⟨ ALM₁._∈_ ⟩₁ xs) × (y ⟨ ALM₂._∈_ ⟩₁ fun x)
  >>=-∈ f = >>=-Any ALM₂.≈-resp-∈ f

  -- _>>=_ is monotone.

  >>=-mono : ∀ (f g : S₁ ⟶ L₂.setoid) {xs ys} →
             xs ⟨ ALM₁._⊆_ ⟩₁ ys →
             (∀ {x} → _⟶_.fun f x ⟨ ALM₂._⊆_ ⟩₁ _⟶_.fun g x) →
             (xs >>= _⟶_.fun f) ⟨ ALM₂._⊆_ ⟩₁ (ys >>= _⟶_.fun g)
  >>=-mono f g {xs} xs⊆ys f⊆g z∈ with >>=-∈ f xs z∈
  ... | (x , x∈xs , z∈fx) = ∈->>= g (xs⊆ys x∈xs) (f⊆g z∈fx)

 module ListMembership₁₂ (S : Setoid) where

  private
    open module L    = ListEq.Equality S using ([]; _∷_)
    module S         = Setoid S
    _→S              = λ (A : Set) → A ≡⇨ λ _ → S
    _→S′             = λ (A : Set) → PropEq.setoid (A → S.carrier)
    module →S {A}    = Setoid (A →S)
    module ALM-≡     = Any.ListMembership-≡
    module ALM       = Any.ListMembership S
    module ALM→S {A} = Any.ListMembership (A →S)

    ret : ∀ {S′} → S′ ⟶ S → S′ ⟶ L.setoid
    ret f = record { fun  = return ∘ _⟶_.fun f
                   ; pres = λ x≈y → _⟶_.pres f x≈y ∷ []
                   }

    ret′ : ∀ {A} → (A → S.carrier) → PropEq.setoid A ⟶ L.setoid
    ret′ f = ret record { fun  = f
                        ; pres = S.reflexive ∘ PropEq.cong f
                        }

    cong : ∀ {A} (xs : List A) {f g} → f ⟨ →S._≈_ ⟩₁ g →
           (xs >>= return ∘ f) ⟨ L._≈_ ⟩₁ (xs >>= return ∘ g)
    cong []       f≈g = []
    cong (x ∷ xs) f≈g = f≈g x ∷ cong xs f≈g

    app : ∀ {A} → List A → (A →S) ⟶ L.setoid
    app xs = record { fun  = λ f' → xs >>= λ x' → return (f' x')
                    ; pres = cong xs
                    }

    app′ : ∀ {A} → List A → (A →S′) ⟶ L.setoid
    app′ xs = record { fun  = _⟶_.fun (app xs)
                     ; pres = L.reflexive ∘
                              PropEq.cong (λ f → xs >>= return ∘ f)
                     }

  -- Introduction and elimination rules for _∈_ on _⊛_.

  ∈-⊛ : ∀ {S′} (f : S′ ⟶ S) {fs xs x} →
        let open _⟶_ f; module LM = Any.ListMembership S′ in
        fun ⟨ ALM→S._∈_ ⟩₁ fs → x ⟨ LM._∈_ ⟩₁ xs →
        fun x ⟨ ALM._∈_ ⟩₁ fs ⊛ xs
  ∈-⊛ {S′} f {fs} {xs} {x} f∈fs x∈xs =
    LM₁.∈->>= (app xs) f∈fs (LM₂.∈->>= (ret f) x∈xs (here S.refl))
    where
    module LM₁ = ListMembership₂₂ (Setoid.carrier S′ →S) S
    module LM₂ = ListMembership₂₂ S′                     S

  ⊛-∈ : ∀ {A} fs (xs : List A) {fx} →
        fx ⟨ ALM._∈_ ⟩₁ fs ⊛ xs →
        ∃₂ λ f x → (f ⟨ ALM-≡._∈_ ⟩₁ fs) ×
                   (x ⟨ ALM-≡._∈_ ⟩₁ xs) ×
                   (fx ⟨ S._≈_ ⟩₁ f x)
  ⊛-∈ {A} fs xs fx∈ with LM.>>=-∈ (app′ xs) fs fx∈
    where module LM = ListMembership₂₂ (A →S′) S
  ... | (f , f∈fs , fx∈′) with LM.>>=-∈ (ret′ f) xs fx∈′
    where module LM = ListMembership₂₂ (PropEq.setoid A) S
  ... | (x , x∈xs , here fx≈fx) = (f , x , f∈fs , x∈xs , fx≈fx)
  ... | (x , x∈xs , there ())

  -- _⊛_ is monotone.

  _⊛-mono_ : ∀ {A} {fs gs} {xs ys : List A} →
             fs ⟨ ALM→S._⊆_ ⟩₁ gs → xs ⟨ ALM-≡._⊆_ ⟩₁ ys →
             fs ⊛ xs ⟨ ALM._⊆_ ⟩₁ gs ⊛ ys
  _⊛-mono_ {fs = fs} {xs = xs} fs⊆gs xs⊆ys fx∈ with ⊛-∈ fs xs fx∈
  ... | (f , x , f∈fs , x∈xs , fx≈fx) = Any.map (S.trans fx≈fx) $
    ∈-⊛ {PropEq.setoid _}
        (record { fun = f; pres = S.reflexive ∘ PropEq.cong f })
        (fs⊆gs (Any.map (λ f≡g x → S.reflexive $
                                     PropEq.cong (λ f → f x) f≡g) f∈fs))
        (xs⊆ys x∈xs)

-- Lemmas related to _∈_, parameterised on underlying equalities.

module ListMembership₁ (S : Setoid) where
  open ListMembership₁₁ S public
  open ListMembership₁₂ S public

module ListMembership₂ (S₁ S₂ : Setoid) where
  open ListMembership₂₁ S₁ S₂ public
  open ListMembership₂₂ S₁ S₂ public

-- The following module instantiates/modifies most of the lemmas from
-- ListMembership₁ and ListMembership₂ for propositional equality.

module ListMembership-≡ where

  open Any.ListMembership-≡
  private
    module P {A} = ListEq.PropositionalEquality {A}
    open module LM₁ {A} = ListMembership₁ (PropEq.setoid A) public
      using (_++-mono_; ++-idempotent; ⊛-∈)
    open module LM₂ {A} {B} =
      ListMembership₂ (PropEq.setoid A) (PropEq.setoid B) public
      using (map-∈)

  -- Any is monotone.

  mono : ∀ {A xs ys} {P : Pred A} → xs ⊆ ys → Any P xs → Any P ys
  mono {P = P} = LM₁.mono (PropEq.subst P)

  -- Introduction and elimination rules for Any on concat.

  Any-concat : ∀ {A} {P : Pred A} {xs xss} →
               Any P xs → xs ∈ xss → Any P (concat xss)
  Any-concat {P = P} p = LM₁.Any-concat (PropEq.subst P) p ∘
                         Any.map P.reflexive

  concat-Any : ∀ {A} {P : Pred A} xss →
               Any P (concat xss) → ∃ λ xs → Any P xs × xs ∈ xss
  concat-Any xss p =
    Prod.map id (Prod.map id (Any.map P.≈⇒≡)) $ LM₁.concat-Any xss p

  -- concat is monotone.

  concat-mono : ∀ {A} {xss yss : List (List A)} →
                xss ⊆ yss → concat xss ⊆ concat yss
  concat-mono xss⊆yss =
    LM₁.concat-mono (Any.map P.reflexive ∘ xss⊆yss ∘ Any.map P.≈⇒≡)

  -- any is monotone.

  any-mono : ∀ {A} (p : A → Bool) {xs ys} →
             xs ⊆ ys → T (any p xs) → T (any p ys)
  any-mono p = LM₁.any-mono p (PropEq.subst (T ∘₀ p))

  -- Introduction rule for _∈_ on map.

  ∈-map : ∀ {A B} {f : A → B} {x xs} →
          x ∈ xs → f x ∈ map f xs
  ∈-map {f = f} = LM₂.∈-map (PropEq.→-to-⟶ f)

  -- map is monotone.

  map-mono : ∀ {A B} {f : A → B} {xs ys} →
             xs ⊆ ys → map f xs ⊆ map f ys
  map-mono {f = f} = LM₂.map-mono (PropEq.→-to-⟶ f)

  -- Introduction and elimination rules for Any on _>>=_.

  Any->>= : ∀ {A B P} (f : A → List B) {x xs} →
            x ∈ xs → Any P (f x) → Any P (xs >>= f)
  Any->>= {P = P} f =
    LM₂.Any->>= (PropEq.subst P)
                (record { fun = f; pres = P.reflexive ∘ PropEq.cong f })

  >>=-Any : ∀ {A B P} (f : A → List B) xs →
            Any P (xs >>= f) → ∃ λ x → x ∈ xs × Any P (f x)
  >>=-Any {P = P} f =
    LM₂.>>=-Any (PropEq.subst P)
                (record { fun = f; pres = P.reflexive ∘ PropEq.cong f })

  -- _>>=_ is monotone.

  _>>=-mono_ : ∀ {A B} {f g : A → List B} {xs ys} →
               xs ⊆ ys → (∀ {x} → f x ⊆ g x) →
               (xs >>= f) ⊆ (ys >>= g)
  _>>=-mono_ {f = f} {g} =
    LM₂.>>=-mono (record { fun = f; pres = P.reflexive ∘ PropEq.cong f })
                 (record { fun = g; pres = P.reflexive ∘ PropEq.cong g })

  -- Introduction rule for _∈_ on _⊛_.

  ∈-⊛ : ∀ {A B} {fs : List (A → B)} {xs f x} →
        f ∈ fs → x ∈ xs → f x ∈ fs ⊛ xs
  ∈-⊛ {f = f} f∈fs =
    LM₁.∈-⊛ (PropEq.→-to-⟶ f)
            (Any.map (λ f≡g x → PropEq.cong (λ f → f x) f≡g) f∈fs)

  -- _⊛_ is monotone.

  _⊛-mono_ : ∀ {A B} {fs gs : List (A → B)} {xs ys} →
             fs ⊆ gs → xs ⊆ ys → fs ⊛ xs ⊆ gs ⊛ ys
  _⊛-mono_ {fs = fs} {gs} fs⊆gs = LM₁._⊛-mono_ helper
    where
    helper : ∀ {f} → Any (_≗_ f) fs → Any (_≗_ f) gs
    helper {f} f∈fs with find f∈fs
    ... | (g , g∈fs , f≗g) =
      Any.map (λ g≡h x → PropEq.subst (λ h → f x ≡ h x) g≡h (f≗g x))
              (fs⊆gs g∈fs)
