{-# OPTIONS_GHC -Wunused-imports #-}

{-|
  Built-in backends.
-}

module Agda.Compiler.Builtin where

import Agda.Compiler.Backend (Backend)

import Agda.Compiler.MAlonzo.Compiler (ghcBackend)
import Agda.Compiler.JS.Compiler (jsBackend)
import Agda.Interaction.Highlighting.Dot (dotBackend)
import Agda.Interaction.Highlighting.HTML (htmlBackend)
import Agda.Interaction.Highlighting.LaTeX (latexBackend)

builtinBackends :: [Backend]
builtinBackends =
  [ ghcBackend
  , jsBackend
  , dotBackend
  , htmlBackend
  , latexBackend
  ]
