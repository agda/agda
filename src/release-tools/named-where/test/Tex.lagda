\documentclass{article}
\begin{document}

A decoy in prose: module Decoy where

\begin{code}
module Tex where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

g : Bool → Nat
g b with b
... | true  = 0
... | false = 1
  module W where
  q : Nat
  q = 1
\end{code}

\end{document}
