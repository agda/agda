-- {-# OPTIONS --no-positivity-check #-}
{-

  Data, Deliberately

  Conor McBride

  Workshop in Dependently Typed Programming
  Nottingham, 2008

  (Agda rendering by Ulf Norell)

-}
module Talk where

open import SomeBasicStuff

-- Codes for (first order) inductive families.
data Code (I : Set) : Set1 where
  arg : (A : Set) -> (A -> Code I) -> Code I
  rec : I -> Code I -> Code I
  out : I -> Code I

-- The semantics of a code is a functor.
⟦_⟧ : {I : Set} -> Code I -> (I -> Set) -> I -> Set
⟦ out i   ⟧ X j = i == j
⟦ arg A B ⟧ X j = Σ A \a -> ⟦ B a ⟧ X j
⟦ rec i C ⟧ X j = X i × ⟦ C ⟧ X j

map : {I : Set}{X Y : I -> Set}(C : Code I) ->
      ({i : I} -> X i -> Y i) ->
      {i : I} -> ⟦ C ⟧ X i -> ⟦ C ⟧ Y i
map (out i)   f x       = x
map (arg A B) f (a , b) = a , map (B a) f b
map (rec i C) f (a , b) = f a , map C f b

-- Tying the recursive knot. The positivity checker won't spot that
-- ⟦ C ⟧ X i is strictly positive i X, so we've switched it off.

-- ASR (08 August 2014): It's not necessary disable the strictly
-- positive checher.
data μ {I : Set}(C : Code I) : I -> Set where
  <_> : forall {i} -> ⟦ C ⟧ (μ C) i -> μ C i

-- Who needs a primitive case-construct anyway?
case_of_ : {A : Set1}{ts : Enumeration} -> Enum ts -> Table A ts -> A
case t of tbl = lookup tbl t

-- The code for lists
`List` : Set -> Code True
`List` X = arg _ \t ->
           case t of
             "nil"  ↦ out _
           ∣ "cons" ↦ arg X (\_ -> rec _ (out _))
           ∣ []

-- The actual list type
List : Set -> Set
List A = μ (`List` A) _

-- We can define the code for vectors directly. However, the point is
-- that we won't have to.
`VecD` : Set -> Code Nat
`VecD` X = arg _ \t ->
           case t of
             "nil"  ↦ out zero
           ∣ "cons" ↦ ( arg Nat \n ->
                        arg X   \_ ->
                        rec n (out (suc n))
                      )
           ∣ []

-- An ornamentation of a datatype adds some new indexing.
data Orn {I : Set}(J : I -> Set) : Code I -> Set1 where
  arg : forall {A B} -> ((a : A) -> Orn J (B a)) -> Orn J (arg A B)
  rec : forall {i C} -> J i -> Orn J C -> Orn J  (rec i C)
  out : forall {i} -> J i -> Orn J (out i)
  new : forall {C} -> (A : Set) -> (A -> Orn J C) -> Orn J C

-- An ornamented datatype is indexed by pairs of the old and the new index.
orn : {I : Set}{J : I -> Set}{C : Code I} -> Orn J C -> Code (Σ I J)
orn (out j)   = out (_ , j)
orn (arg B)   = arg _ \a -> orn (B a)
orn (new A B) = arg A \a -> orn (B a)
orn (rec j C) = rec (_ , j) (orn C)

-- We can forget the ornamentation and recover an element of the original type.
forget' : {I : Set}{J : I -> Set}{C : Code I}{i : I}{j : J i}
          {X : Σ I J -> Set}{Y : I -> Set} ->
          ({i : I}{j : J i} -> X (i , j) -> Y i) ->
          (ΔC : Orn J C) -> ⟦ orn ΔC ⟧ X (i , j) -> ⟦ C ⟧ Y i
forget' φ (out j)   refl    = refl
forget' φ (arg B)   (a , b) = a , forget' φ (B a) b
forget' φ (new A B) (a , b) = forget' φ (B a) b
forget' φ (rec j C) (a , b) = φ a , forget' φ C b

-- The termination checker runs into the same problem as the positivity
-- checker--it can't tell that forget' φ C x is only applying φ to
-- things smaller than x.

-- ASR (08 August 2014): Added the {-# NO_TERMINATION_CHECK #-}
-- pragma.

{-# NO_TERMINATION_CHECK #-}
forget : {I : Set}{J : I -> Set}{C : Code I}{i : I}{j : J i}
         (ΔC : Orn J C) -> μ (orn ΔC) (i , j) -> μ C i
forget ΔC < x > = < forget' (forget ΔC) ΔC x >

-- A C-algebra over X takes us from ⟦ C ⟧ X i to X i.
Alg : {I : Set} -> Code I -> (I -> Set) -> Set
Alg C X = forall i -> ⟦ C ⟧ X i -> X i

-- We can fold by an algebra.

-- ASR (08 August 2014): Added the {-# NO_TERMINATION_CHECK #-}
-- pragma.

{-# NO_TERMINATION_CHECK #-}
fold : {I : Set}{X : I -> Set}{C : Code I} ->
       Alg C X -> {i : I} -> μ C i -> X i
fold {C = C} φ < x > = φ _ (map C (fold φ) x)

-- A type can be ornamented an arbitrary algebra over its functor.
decorate : {I : Set}{X : I -> Set}(C : Code I)
           (φ : Alg C X) -> Orn X C
decorate         (out i)   φ = out (φ i refl)
decorate         (arg A B) φ = arg \a -> decorate (B a) (\i b -> φ i (a , b))
decorate {X = X} (rec i C) φ = new (X i) \x -> rec x (decorate C \i b -> φ i (x , b))

-- Main theorem: If you have an element in a type decorated by φ, you
-- can recover forgotten decorations by folding with φ. Specialised to
-- lists and vectors we get
--   ∀ xs : Vec A n. length (forget xs) == n.
-- Two-level definition as usual.
thm' : {I : Set}{X J : I -> Set}{Y : Σ I J -> Set}
       (C : Code I){i : I}{j : J i}(φ : Alg C J)
       (F : {i : I} -> X i -> J i)
       (ψ : {i : I}{j : J i} -> Y (i , j) -> X i) ->
       ({i : I}{j : J i}(z : Y (i , j)) -> F (ψ z) == j) ->
       let ΔC = decorate C φ in
       (x : ⟦ orn ΔC ⟧ Y (i , j)) ->
       φ i (map C F (forget' ψ ΔC x)) == j
thm' (out i)   φ F ψ ih refl        = refl
thm' (arg A B) φ F ψ ih (a , b)     = thm' (B a) (\i b -> φ i (a , b)) F ψ ih b
thm' (rec i C) {i = i0}{j = j0} φ F ψ ih (j , x , c)
  with F (ψ x) | ih x | thm' C (\i b -> φ i (j , b)) F ψ ih c
... | .j | refl | rest = rest

-- ASR (08 August 2014): Added the {-# NO_TERMINATION_CHECK #-}
-- pragma.

{-# NO_TERMINATION_CHECK #-}
thm : {I : Set}{J : I -> Set}(C : Code I){i : I}{j : J i}(φ : Alg C J) ->
      (x : μ (orn (decorate C φ)) (i , j)) ->
      fold φ (forget (decorate C φ) x) == j
thm C φ < x > = thm' C φ (fold φ) (forget (decorate C φ)) (thm C φ) x

-- Vectors as decorated lists.

lengthAlg : {A : Set} -> Alg (`List` A) (\_ -> Nat)
lengthAlg _ (enum ."nil"  zero , _)               = zero
lengthAlg _ (enum ."cons" (suc zero) , x , n , _) = suc n
lengthAlg _ (enum _ (suc (suc ())) , _)

length : {A : Set} -> List A -> Nat
length = fold lengthAlg

-- Now vectors are really lists decorated by their length.
`Vec` : (A : Set) -> Orn (\_ -> Nat) (`List` A)
`Vec` A = decorate (`List` A) lengthAlg

Vec : Set -> Nat -> Set
Vec A n = μ (orn (`Vec` A)) (_ , n)

nil : {A : Set} -> Vec A zero
nil = < enum "nil" zero , refl >

cons : {A : Set}{n : Nat} -> A -> Vec A n -> Vec A (suc n)
cons {n = n} x xs = < enum "cons" (suc zero) , x , n , xs , refl >

-- The proof that the index of the vector is really the length follows directly
-- from our main theorem.
corollary : {A : Set}{n : Nat}(xs : Vec A n) ->
            length (forget (`Vec` _) xs) == n
corollary = thm (`List` _) lengthAlg
