{-# OPTIONS --prop --type-in-type #-}

record × (A B : Prop) : Prop where
  field
    fst : A
    snd : B
