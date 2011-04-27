{-# LANGUAGE EmptyDataDecls #-}

module Data.FFI where

type AgdaList a b = [b]
type AgdaMaybe a b = Maybe b
type AgdaEither a b c d = Either c d

data AgdaEmpty

data AgdaStream a = Cons a (AgdaStream a)
