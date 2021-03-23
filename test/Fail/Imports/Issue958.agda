
module Imports.Issue958 where

postulate FunctorOps : Set
module FunctorOps (ops : FunctorOps) where
  postulate map : Set

postulate IsFunctor : Set
module IsFunctor (fun : IsFunctor) where
  postulate ops : FunctorOps
  open FunctorOps ops public
