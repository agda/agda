
data Type : Set where
  A B : Type

f : Type → Type → Type
f A t = t
f t = {!t!}

-- WAS: Case-splitting t yields an internal error on Agda/TypeChecking/Coverage.hs:467

-- SHOULD: produce the following definition:
-- f : Type → Type → Type
-- f A t = t
-- f B = {!!}
