{-|
  Built-in backends.
-}

module Agda.Compiler.Builtin where

import Agda.Compiler.Backend (Backend)

import Agda.Compiler.MAlonzo.Compiler (ghcBackend)
import Agda.Compiler.JS.Compiler (jsBackend)
import Agda.Interaction.Highlighting.Dot (dotBackend)

builtinBackends :: [Backend]
builtinBackends =
  [ ghcBackend
  , jsBackend
  , dotBackend
  ]
