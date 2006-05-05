
module test.simple where

postulate
  A   : Set
--   idA : A -> A
--   F   : Set -> Set
--   H   : (A,B:Set) -> Prop
--   id  : (A:Set) -> A -> A
--   idH : {A:Set} -> A -> A
--   fa  : F A
  a   : A

-- test1 = id (F A) fa
-- test2 = idH fa
-- test3 = id _ fa
-- test4 = idH {! foo bar !}
-- test5 = id id	-- we can't do this (on purpose)!

id = \{A:Set}(x:A) -> x

test = id a

module prop where

  postulate
    (\/)  : Prop -> Prop -> Prop
    inl	  : {P,Q:Prop} -> P -> P \/ Q
    inr	  : {P,Q:Prop} -> Q -> P \/ Q
    orE	  : {P,Q,R:Prop} -> P \/ Q -> (P -> R) -> (Q -> R) -> R
    False : Prop
    (==>) : Prop -> Prop -> Prop
    impI  : {P,Q:Prop} -> (P -> Q) -> P ==> Q
    impE  : {P,Q:Prop} -> P ==> Q -> P -> Q

  Not = \(P:Prop) -> P ==> False

  notnotEM = \(P:Prop) ->
    impI (\ (nEM : Not (P \/ Not P)) ->
	    impE nEM (
		inr (
		  impI (\ p ->
		    impE nEM (inl p)
		  )
		)
	      )
	    )


