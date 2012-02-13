-- {-# OPTIONS --verbose tc.proj.like:100 #-}

-- Apparently, there can be projection like functions working on arguments of type Axiom.
module Issue558c where

data ⊤ : Set where
  tt : ⊤

data V : Set where
  aV : ⊤ → V

postulate D : ⊤ → Set
          zero : D tt
          suc : ∀ {t} → D t → V

test : {{v : V}} → ⊤
test {{v}} = tt

module test {t : ⊤} {d : D t} where
  inst : V
  inst = aV tt

  someT : ⊤
  someT = test
