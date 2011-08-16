-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}

module 01-arguments where

data T : Set where
  tt : T

data A : Set where
  mkA : A
  mkA2 : T → A

giveA : ⦃ a : A ⦄ → A
giveA {{a}} = a

test : A → T
test a = tt

test2 : T
test2 = test giveA

id : {A : Set} → A → A
id v = v

test5 : T → T
test5 = id

⋯ : {A : Set} → {{a : A}} → A
⋯ {{a}} = a

--giveA' : {{a : A}} → A
--giveA' = ⋯

