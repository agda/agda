module Termination.Sized.DeBruijnBase where

open import Data.Maybe
open import Data.Maybe.Effectful
open import Function -- composition, identity
open import Relation.Binary.PropositionalEquality hiding ( subst )
open ≡-Reasoning

open import Effect.Functor

fmap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
fmap = RawFunctor._<$>_ functor

-- OR:
-- open RawFunctor MaybeFunctor using () renaming (_<$>_ to fmap)

fmapExt : {A B : Set}{f g : A -> B} ->
          (forall a -> f a ≡ g a) -> forall m -> fmap f m ≡ fmap g m
fmapExt f≡g nothing  = refl
fmapExt f≡g (just a) = cong just (f≡g a)

fmapLaw1 : {A : Set}(a : Maybe A) -> fmap id a ≡ a
fmapLaw1 nothing  = refl
fmapLaw1 (just a) = refl

fmapLaw2 : {A B C : Set}(f : B -> C)(g : A -> B) ->
          forall m -> fmap f (fmap g m) ≡ fmap (f ∘ g) m
fmapLaw2 f g nothing  = refl
fmapLaw2 f g (just a) = refl

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

lamExt : {A B : Set}{f g : A -> B} ->
         (forall a -> f a ≡ g a) -> forall t -> lam f t ≡ lam g t
lamExt f≡g (var a)   = cong var (f≡g a)
lamExt f≡g (abs r)   = cong abs (lamExt (fmapExt f≡g) r)
lamExt f≡g (app r s) = cong₂ app (lamExt f≡g r) (lamExt f≡g s)

lamLaw1 : {A : Set}(t : Lam A) -> lam id t ≡ t
lamLaw1 (var a) = refl
lamLaw1 (app r s) = begin
  lam id (app r s)
     ≡⟨ refl ⟩
  app (lam id r) (lam id s)
     ≡⟨ cong (app (lam id r)) (lamLaw1 s) ⟩
  app (lam id r) s
     ≡⟨ cong (\ x -> app x s) (lamLaw1 r) ⟩
  app r s
     ∎
lamLaw1 (abs t) = begin
  lam id (abs t)
     ≡⟨ refl ⟩
  abs (lam (fmap id) t)
     ≡⟨ cong abs (lamExt {g = id} fmapLaw1 t) ⟩
  abs (lam id t)
     ≡⟨ cong abs (lamLaw1 t) ⟩
  abs t
     ∎

lamLaw2 : {A B C : Set}(f : B -> C)(g : A -> B) ->
          forall t -> lam f (lam g t) ≡ lam (f ∘ g) t
lamLaw2 f g (var a)   = refl
lamLaw2 f g (app r s) = cong₂ app (lamLaw2 f g r) (lamLaw2 f g s)
lamLaw2 f g (abs t)   = begin
  lam f (lam g (abs t))
     ≡⟨ refl ⟩
  lam f (abs (lam (fmap g) t))
     ≡⟨ refl ⟩
  abs (lam (fmap f) (lam (fmap g) t))
     ≡⟨ cong abs (lamLaw2 (fmap f) (fmap g) t) ⟩
  abs (lam (fmap f ∘ fmap g) t)
     ≡⟨ cong abs (lamExt (fmapLaw2 f g) t) ⟩
  abs (lam (fmap (f ∘ g)) t)
     ≡⟨ refl ⟩
  lam (f ∘ g) (abs t)
     ∎

-- lifting a substitution A -> Lam B under a binder
lift : {A B : Set} -> (A -> Lam B) -> Maybe A -> Lam (Maybe B)
lift f nothing  = var nothing
lift f (just a) = lam just (f a)

-- extensionality of lifting
liftExt : {A B : Set}{f g : A -> Lam B} ->
   ((a : A) -> f a ≡ g a) -> (t : Maybe A) -> lift f t ≡ lift g t
liftExt H nothing  = refl
liftExt H (just a) = cong (lam just) $ H a

-- simultaneous substitution
subst : {A B : Set} -> (A -> Lam B) -> Lam A -> Lam B
subst f (var a)     = f a
subst f (app t1 t2) = app (subst f t1) (subst f t2)
subst f (abs r)     = abs (subst (lift f) r)

-- extensionality of subst
substExt : {A B : Set}{f g : A -> Lam B} ->
   ((a : A) -> f a ≡ g a) -> (t : Lam A) -> subst f t ≡ subst g t
substExt H (var a)     = H a
substExt {f = f}{g = g} H (app t1 t2) = begin
  subst f (app t1 t2)
     ≡⟨ refl ⟩
  app (subst f t1) (subst f t2)
     ≡⟨ cong (\ x -> app x (subst f t2)) (substExt H t1) ⟩
  app (subst g t1) (subst f t2)
     ≡⟨ cong (\ x -> app (subst g t1) x) (substExt H t2) ⟩
  app (subst g t1) (subst g t2)
     ∎
substExt {f = f}{g = g} H (abs r) = begin
  subst f (abs r)
     ≡⟨ refl ⟩
  abs (subst (lift f) r)
     ≡⟨ cong abs (substExt (liftExt H) r) ⟩
  abs (subst (lift g) r)
     ≡⟨ refl ⟩
  subst g (abs r)
     ∎

-- Lemma: lift g ∘ fmap f = lift (g ∘ f)
liftLaw1 : {A B C : Set}(f : A -> B)(g : B -> Lam C)(t : Maybe A) ->
  lift g (fmap f t) ≡ lift (g ∘ f) t
liftLaw1 f g nothing = begin
  lift g (fmap f nothing)
     ≡⟨ refl ⟩
  lift g nothing
     ≡⟨ refl ⟩
  var nothing
     ≡⟨ refl ⟩
  lift (g ∘ f) nothing
     ∎
liftLaw1 f g (just a) = begin
  lift g (fmap f (just a))
     ≡⟨ refl ⟩
  lift g (just (f a))
     ≡⟨ refl ⟩
  lam just (g (f a))
     ≡⟨ refl ⟩
  lift (g ∘ f) (just a)
     ∎

-- Lemma: subst g ∘ lam f t = subst (g ∘ f)
substLaw1 : {A B C : Set}(f : A -> B)(g : B -> Lam C)(t : Lam A) ->
  subst g (lam f t) ≡ subst (g ∘ f) t

substLaw1 f g (var a) = refl

substLaw1 f g (app t1 t2) = begin
  subst g (lam f (app t1 t2))
     ≡⟨ refl ⟩
  subst g (app (lam f t1) (lam f t2))
     ≡⟨ refl ⟩
  app (subst g (lam f t1)) (subst g (lam f t2))
     ≡⟨ cong (\ x -> app x (subst g (lam f t2))) (substLaw1 f g t1) ⟩
  app (subst (g ∘ f) t1) (subst g (lam f t2))
     ≡⟨ cong (\ x -> app (subst (g ∘ f) t1) x) (substLaw1 f g t2) ⟩
  app (subst (g ∘ f) t1) (subst (g ∘ f) t2)
     ∎

substLaw1 f g (abs r) =
  begin subst g (lam f (abs r))
     ≡⟨ refl ⟩
  subst g (abs (lam (fmap f) r))
     ≡⟨ refl ⟩
  abs (subst (lift g) (lam (fmap f) r))
     ≡⟨ cong abs (substLaw1 (fmap f) (lift g) r) ⟩
  abs (subst (lift g ∘ fmap f) r)
     ≡⟨ cong abs (substExt {f = lift g ∘ fmap f} {g = lift (g ∘ f)} (liftLaw1 f g) r) ⟩
  abs (subst (lift (g ∘ f)) r)
     ∎

-- Lemma: lift (lam f ∘ g) = lam f ∘ subst g
liftLaw2 : {A B C : Set}(f : B -> C)(g : A -> Lam B)(t : Maybe A) ->
  lift (lam f ∘ g) t ≡ lam (fmap f) (lift g t)
liftLaw2 f g nothing = begin
  lift (lam f ∘ g) nothing
     ≡⟨ refl ⟩
  var nothing
     ≡⟨ refl ⟩
  var (fmap f nothing)
     ≡⟨ refl ⟩
  lam (fmap f) (var nothing)
     ≡⟨ refl ⟩
  lam (fmap f) (lift g nothing)
     ∎
liftLaw2 f g (just a) = begin
  lift (lam f ∘ g) (just a)
     ≡⟨ refl ⟩
  lam just (lam f (g a))
     ≡⟨ lamLaw2 just f (g a) ⟩
  lam (just ∘ f) (g a)
     ≡⟨ lamExt (\ a -> refl) (g a) ⟩
  lam (fmap f ∘ just) (g a)
     ≡⟨ sym (lamLaw2 (fmap f) just (g a)) ⟩
  lam (fmap f) (lam just (g a))
     ≡⟨ refl ⟩
  lam (fmap f) (lift g (just a))
     ∎


-- Lemma: subst (lam f ∘ g) = lam f ∘ subst g
substLaw2 : {A B C : Set}(f : B -> C)(g : A -> Lam B)(t : Lam A) ->
  subst (lam f ∘ g) t ≡ lam f (subst g t)

substLaw2 f g (var a) = refl

substLaw2 f g (app r s) = begin
  subst (lam f ∘ g) (app r s)
     ≡⟨ refl ⟩
  app (subst (lam f ∘ g) r) (subst (lam f ∘ g) s)
     ≡⟨ cong (app (subst (lam f ∘ g) r)) (substLaw2 f g s) ⟩
  app (subst (lam f ∘ g) r) (lam f (subst g s))
     ≡⟨ cong (\ x -> app x (lam f (subst g s))) (substLaw2 f g r) ⟩
  app (lam f (subst g r)) (lam f (subst g s))
     ≡⟨ refl ⟩
  lam f (app (subst g r) (subst g s))
     ≡⟨ refl ⟩
  lam f (subst g (app r s))
     ∎

substLaw2 f g (abs t) = begin
  subst (lam f ∘ g) (abs t)
     ≡⟨ refl ⟩
  abs (subst (lift (lam f ∘ g)) t)
     ≡⟨ cong abs (substExt (liftLaw2 f g) t) ⟩
  abs (subst (lam (fmap f) ∘ (lift g)) t)
     ≡⟨ cong abs (substLaw2 (fmap f) (lift g) t) ⟩
  abs (lam (fmap f) (subst (lift g) t))
     ≡⟨ refl ⟩
  lam f (abs (subst (lift g) t))
     ≡⟨ refl ⟩
  lam f (subst g (abs t))
     ∎
