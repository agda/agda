module NoParseForLHS where

data X : Set where
  _! : X -> X
  z  : X

right : X -> X
right (x !) = x
right z     = z !

wrong : X -> X
wrong (! x) = x
wrong z     = z !

