-- 2010-11-16
-- compactification of Data.Set.Decoration.gmapAll
--
-- This test case fails if we remove instantiateFull
-- (and with it eta-contraction) from definition bodies in Def.hs
-- see Issue 361

-- {-# OPTIONS -v tc.polarity:15 -v tc.pos:25 #-}

module EtaContractionDefBody where

------------------------------------------------------------------------
-- Binary relations

-- Homogeneous binary relations

Rel : Set → Set1
Rel A = A → A → Set

-- Generalised implication. If P ≡ Q it can be read as "f preserves
-- P".

_=[_]⇒_ : {A B : Set} →
          Rel A → (A → B) → Rel B → Set
P =[ f ]⇒ Q = ∀ {x y} → P x y → Q (f x) (f y)


record Σ₂ {A B : Set}
                (T : A → B → Set) : Set  where
  constructor pack₂
  field
    {x}   : A
    {y}   : B
    proof : T x y

-- Data.Star

infixr 5 _◅_

-- Reflexive transitive closure.

data Star {I : Set} (T : Rel I) : Rel I where
  ε   : ∀ {i} → Star T i i
  _◅_ : ∀ {i j k} (x : T i j) (xs : Star T j k) → Star T i k
        -- The type of _◅_ is Trans T (Star T) (Star T); I expanded
        -- the definition in order to be able to name the arguments (x
        -- and xs).

-- A generalised variant of map which allows the index type to change.

gmap : ∀ {I} {T : Rel I} {J} {U : Rel J} →
       (f : I → J) → T =[ f ]⇒ U → Star T =[ f ]⇒ Star U
gmap f g ε        = ε
gmap f g (x ◅ xs) = g x ◅ gmap f g xs

-- Data.Star.Decoration

EdgePred : ∀ {I} → Rel I → Set₁
EdgePred T = ∀ {i j} → T i j → Set

-- Decorating an edge with more information.

data DecoratedWith {I : Set} {T : Rel I} (P : EdgePred T)
       : Rel (Σ₂ (Star T)) where
  ↦ : ∀ {i j k} {x : T i j} {xs : Star T j k}
      (p : P x) → DecoratedWith P (pack₂ (x ◅ xs)) (pack₂ xs)

-- Star-lists decorated with extra information. All P xs means that
-- all edges in xs satisfy P.

All : ∀ {I} {T : Rel I} → EdgePred T → EdgePred (Star T)
All P {j = j} xs =
  Star (DecoratedWith P) (pack₂ xs) (pack₂ {y = j} ε)

-- We can map over decorated vectors.

gmapAll : ∀ {I} {T : Rel I} {P : EdgePred T}
                {J} {U : Rel J} {Q : EdgePred U}
                {i j} {xs : Star T i j}
          (f : I → J) (g : T =[ f ]⇒ U) →
          (∀ {i j} {x : T i j} → P x → Q (g x)) →
          All P xs → All {T = U} Q (gmap f g xs)
gmapAll f g h ε          = ε
gmapAll f g h (↦ x ◅ xs) = ↦ (h x) ◅ gmapAll f g h xs

{- THIS WOULD BE THE ERROR MESSAGE:
/Users/abel/cover/alfa/Agda2/test/succeed/EtaContractionDefBody.agda:76,15-16
xs != ε of type Star (λ .i' .j → T .i' .j) j j
when checking that the pattern ε has type
Star (DecoratedWith (λ {.i} {.j} → P)) (pack₂ xs) (pack₂ ε)
-}
