module DeBruijn where

open import Prelude -- using (_∘_)       -- composition, identity
open import Data.Maybe
open import Logic.Identity renaming (subst to subst≡)
import Logic.ChainReasoning
module Chain = Logic.ChainReasoning.Poly.Homogenous _≡_ (\x -> refl) (\x y z -> trans)
open Chain

-- untyped de Bruijn terms 
data Lam (A : Set) : Set where
    var : A -> Lam A
    app : Lam A -> Lam A -> Lam A
    abs : Lam (Maybe A) -> Lam A

-- functoriality of Lam 
lam : {A B : Set} -> (A -> B) -> Lam A -> Lam B
lam f (var a)     = var (f a)
lam f (app t1 t2) = app (lam f t1) (lam f t2)
lam f (abs r)     = abs (lam (fmap f) r)

-- lifting a substitution A -> Lam B under a binder
lift : {A B : Set} -> (A -> Lam B) -> Maybe A -> Lam (Maybe B)
lift f nothing  = var nothing
lift f (just a) = lam just (f a)

-- extensionality of lifting
liftExt : {A B : Set}(f g : A -> Lam B) ->
   ((a : A) -> f a ≡ g a) -> (t : Maybe A) -> lift f t ≡ lift g t
liftExt f g H nothing  = refl
liftExt f g H (just a) = cong (lam just) $ H a

-- simultaneous substitution
subst : {A B : Set} -> (A -> Lam B) -> Lam A -> Lam B
subst f (var a)     = f a
subst f (app t1 t2) = app (subst f t1) (subst f t2)
subst f (abs r)     = abs (subst (lift f) r)

-- extensionality of subst
substExt : {A B : Set}(f g : A -> Lam B) ->
   ((a : A) -> f a ≡ g a) -> (t : Lam A) -> subst f t ≡ subst g t
substExt f g H (var a)     = H a
substExt f g H (app t1 t2) = 
  chain> subst f (app t1 t2)
     === app (subst f t1) (subst f t2)
       by refl 
     === app (subst g t1) (subst f t2)
       by cong (\ x -> app x (subst f t2)) (substExt f g H t1)
     === app (subst g t1) (subst g t2)
       by cong (\ x -> app (subst g t1) x) (substExt f g H t2)
substExt f g H (abs r) =
  chain> subst f (abs r)
     === abs (subst (lift f) r)  
       by refl
     === abs (subst (lift g) r)  
       by cong abs (substExt (lift f) (lift g) (liftExt f g H) r)
     === subst g (abs r)
       by refl

-- Lemma: lift g ∘ fmap f = lift (g ∘ f)
liftLaw1 : {A B C : Set}(f : A -> B)(g : B -> Lam C)(t : Maybe A) ->
  lift g (fmap f t) ≡ lift (g ∘ f) t
liftLaw1 f g nothing = 
  chain> lift g (fmap f nothing) 
     === lift g nothing          by refl
     === var nothing             by refl
     === lift (g ∘ f) nothing    by refl
liftLaw1 f g (just a) =
  chain> lift g (fmap f (just a))
     === lift g (just (f a))     by refl
     === lam just (g (f a))      by refl
     === lift (g ∘ f) (just a)   by refl

-- Lemma: subst g (lam f t) = subst (g ∘ f) t
substLaw1 : {A B C : Set}(f : A -> B)(g : B -> Lam C)(t : Lam A) -> 
  subst g (lam f t) ≡ subst (g ∘ f) t

substLaw1 f g (var a) = refl

substLaw1 f g (app t1 t2) = 
  chain> subst g (lam f (app t1 t2))
     === subst g (app (lam f t1) (lam f t2))            
       by refl
     === app (subst g (lam f t1)) (subst g (lam f t2))  
       by refl
     === app (subst (g ∘ f) t1) (subst g (lam f t2))    
       by cong (\ x -> app x (subst g (lam f t2))) (substLaw1 f g t1)
     === app (subst (g ∘ f) t1) (subst (g ∘ f) t2) 
       by cong (\ x -> app (subst (g ∘ f) t1) x) (substLaw1 f g t2)

substLaw1 f g (abs r) =
  chain> subst g (lam f (abs r))
     === subst g (abs (lam (fmap f) r))
       by refl
     === abs (subst (lift g) (lam (fmap f) r))
       by refl
     === abs (subst (lift g ∘ fmap f) r)
       by cong abs (substLaw1 (fmap f) (lift g) r)
     === abs (subst (lift (g ∘ f)) r)
       by cong abs (substExt (lift g ∘ fmap f) (lift (g ∘ f)) (liftLaw1 f g) r)

-- Lemma: subst (lam f ∘ g) = lam f ∘ subst g
substLaw2 : {A B C : Set}(f : B -> C)(g : A -> Lam B)(t : Lam A) ->
  subst (lam f ∘ g) t ≡ lam f (subst g t)
substLaw2 f g (var a) = refl 
