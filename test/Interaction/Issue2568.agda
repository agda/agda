
postulate
  A : Set
  T : A → Set
  g : {{a : A}} → Set → T a

test : {{a b : A}} → Set
test {{a}} {{b}} = {!g A!} -- C-u C-u C-c C-d gives T b
