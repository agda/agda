-- Testing termination using subpatterns
module TerminationSubpattern where

-- a list with two different conses
data EOList (A : Set) : Set where
    Nil : EOList A
    ECons : A -> EOList A -> EOList A
    OCons : A -> EOList A -> EOList A


butLastWithDefault : {A : Set} -> A -> EOList A -> A
butLastWithDefault a Nil = a
butLastWithDefault a (ECons b l) = butLastWithDefault b l
butLastWithDefault a (OCons b l) = butLastWithDefault b l


-- a very stupid implementation:
butLastWithDefault' : {A : Set} -> A -> EOList A -> A
butLastWithDefault' a Nil = a
butLastWithDefault' a (ECons b Nil) = b
butLastWithDefault' a (OCons b Nil) = b
butLastWithDefault' a (ECons b (OCons c l)) = butLastWithDefault' b (OCons c l)
butLastWithDefault' a (ECons b (ECons c l)) = butLastWithDefault' b (ECons c l)
butLastWithDefault' a (OCons b (OCons c l)) = butLastWithDefault' b (OCons c l)
butLastWithDefault' a (OCons b (ECons c l)) = butLastWithDefault' b (ECons c l)

-- terminates, because, e.g. in the last line
--
--   ECons c l   is a subpattern of   OCons b (ECons c l)

-- another justification is with structured orders
-- if all constructors are considered equivalent

