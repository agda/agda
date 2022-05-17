{-# OPTIONS --two-level #-}

open import Agda.Primitive

data Unit : Set where tt : Unit
data Unitω : Setω where tt : Unitω
data SUnit : SSet where tt : SUnit
data SUnitω : SSetω where tt : SUnitω

-- Cannot eliminate fibrant type Unit
-- unless target type is also fibrant
-- f1 : Unit → SUnit
-- f1 tt = tt

-- Cannot eliminate fibrant type Unit
-- unless target type is also fibrant
-- f2 : Unit → SUnitω
-- f2 tt = tt

f3 : Unitω → SUnit
f3 tt = tt

--f4 : Unitω → SUnitω
--f4 tt = tt
