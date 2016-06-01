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

habs eshabs eshpabs eshpabs2 : Set → {_ : ⊥} → Set
habs     = λ _ → λ{}

eshabs   = λ _ → λ { {}}
eshpabs  = λ _ → λ { {()}}
eshpabs2 = λ _ → λ { {(())}}

-- instance

iabs esiabs esipabs esipabs2 : Set → {{_ : ⊥}} → Set
iabs     = λ _ → λ{{}}

esiabs   = λ _ → λ{ {{}}}
esipabs  = λ _ → λ{ {{()}}}
esipabs2 = λ _ → λ{ {{(())}}}
