-- The type checker was a little too eager to prune metavariables in
-- order to get the occurs check to pass. In this particular case it
-- got the constraint
--   _41 A B x == B (_42 A B (x , y))
-- and tried to make it work by pruning the third argument to _42. The
-- correct solution _42 A B p := fst p was thus lost.
module Issue458 where

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) (y : B x) → Σ A B

uncurry : {A : Set} {B : A → Set} {P : Σ A B → Set} →
          ((x : A) (y : B x) → P (x , y)) →
          (p : Σ A B) → P p
uncurry f (x , y) = f x y

fst : {A : Set} {B : A → Set} → Σ A B → A
fst = uncurry λ x y → x

snd : {A : Set} {B : A → Set} (p : Σ A B) → B (fst p)
snd = uncurry λ x y → y

-- Bug.agda:15,7-24
-- Cannot instantiate the metavariable _50 to .B x since it contains
-- the variable x which is not in scope of the metavariable
-- when checking that the expression uncurry (λ x y → y) has type
-- (p : Σ .A .B) → .B (fst p)