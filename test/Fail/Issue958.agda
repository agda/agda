
postulate FunctorOps : Set
module FunctorOps (ops : FunctorOps) where
  postulate map : Set

postulate IsFunctor : Set
module IsFunctor (fun : IsFunctor) where
  postulate ops : FunctorOps
  open FunctorOps ops public
  -- inside here `FunctorOps.map ops` gets printed as `map`

open IsFunctor

-- out here it should too
test : (F : IsFunctor) → FunctorOps.map (ops F)
test F = F

-- EXPECTED: IsFunctor !=< map F
