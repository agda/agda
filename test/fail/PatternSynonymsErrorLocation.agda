{-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --guardedness-preserving-type-constructors #-}

module PatternSynonymsErrorLocation where

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

infixr 2 _,_

record Unit : Set where

data Sigma (A : Set)(B : A -> Set) : Set where
  _,_ : (fst : A) -> B fst -> Sigma A B

-- Prod does not communicate guardedness
Prod : (A B : Set) -> Set
Prod A B = Sigma A \ _ -> B

data Empty : Set where

data ListTag : Set where nil cons : ListTag

{-# NO_TERMINATION_CHECK #-}
List : (A : Set) -> Set
List A = Sigma ListTag T where
  T : ListTag -> Set
  T nil  = Unit
  T cons = Sigma A \ _ -> List A

infix 5 _∷_

pattern []       = nil , _
pattern _∷_ x xs = cons , x , xs
-- FAILS: pattern x ∷ xs = cons , x , xs

data TyTag : Set where base arr : TyTag

{-# NO_TERMINATION_CHECK #-}
Ty : Set
Ty = Sigma TyTag T where
  T : TyTag -> Set
  T base = Unit
  T arr  = Sigma Ty \ _ -> Ty  -- Prod Ty Ty

infix 10 _⇒_

pattern ★       = base , _
pattern _⇒_ A B = arr , A , B

Context = List Ty

data NatTag : Set where zero succ : NatTag

Var : (Gamma : Context)(C : Ty) -> Set
Var []           C = Empty
Var (cons , A , Gamma) C =  Sigma NatTag T
  where T : NatTag -> Set
        T zero = A ≡ C
        T succ = Var Gamma C

pattern vz   = zero , refl
pattern vs x = succ , x

idVar : (Gamma : Context)(C : Ty)(x : Var Gamma C) -> Var Gamma C
idVar [] _ ()
-- CORRECT: idVar (A ∷ Gamma) C (zero , proof) = zero , proof
idVar (A ∷ Gamma) C vz         = vz
idVar (A ∷ Gamma) C (vs x)     = vs (idVar Gamma C x)
