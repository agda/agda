
module Abstract where

data Bool : Set where
  true false : Bool

not : Bool → Bool
not true  = false
not false = true

abstract
  Answer : Set
  Answer = Bool

  yes : Answer
  yes = true

  no : Answer
  no = false

  contradict : Answer → Answer
  contradict x = not x

counter-contradict : Answer → Answer
counter-contradict x = contradict (contradict x)

no-way : Answer
no-way = contradict yes

data Answers : Set where
  one-answer   : Answer → Answers
  more-answers : Answer → Answers → Answers

yes-or-no : Answers
yes-or-no = more-answers yes (one-answer no)
