module Issue1985c where

module Def where
  postulate A : Set

module Par1 (B : Set₁) where
  module Par2 (C : Set₁) where
    open Def public

module Test1 where
  open Par1.Par2 Set Set
  test : Set
  test = A

module Bar = Par1 Set

module Test2 where
  open Bar.Par2
  test : Set
  test = A

module Test3 where
  open Bar.Par2 Set
  test : Set
  test = A

module Baz = Par1

module Test4 where
  open Baz.Par2
  test : Set
  test = A

module Test5 where
  open Baz.Par2 Set
  test : Set
  test = A

module Test6 where
  open Baz.Par2 Set Set
  test : Set
  test = A
