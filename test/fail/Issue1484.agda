-- Andreas, 2015-05-06

module Issue1484 where

data ⊥ : Set where

-- Smörgåsbord of legal absurd lambdas

-- non-hidden

abs esabs eabs eabs2 eabs3 : ⊥ → Set
abs = λ()

esabs = λ{ ()}
eabs  = λ{()}
eabs2 = λ{(())}
eabs3 = λ{((()))}

-- hidden

habs eshabs eshpabs eshpabs2 : {_ : ⊥} → Set
habs     = λ{}

eshabs   = λ{ {}}
eshpabs  = λ{ {()}}
eshpabs2 = λ{ {(())}}

-- instance

iabs esiabs esipabs esipabs2 : {{_ : ⊥}} → Set
iabs     = λ{{}}

esiabs   = λ{ {{}}}
esipabs  = λ{ {{()}}}
esipabs2 = λ{ {{(())}}}

-- The following could maybe parse, but does not.

fails  : {_ : ⊥} → Set
fails = λ{{()}}

-- Error WAS:
-- Internal parser error: Empty LamBindsAbsurd. Please report this as a bug.
