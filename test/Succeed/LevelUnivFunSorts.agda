{-# OPTIONS --level-universe --prop #-}

open import Common.Level
open import Agda.Primitive

_ : LevelUniv
_ = Level
_ : LevelUniv
_ = Level -> Level
_ : Setω2
_ = Level -> Setω1
_ : Setω
_ = Level -> Set
_ : Setω2
_ = Setω1 -> Level
-- should this really work ?
_ = Set -> Level

