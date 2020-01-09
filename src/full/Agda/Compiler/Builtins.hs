module Agda.Compiler.Builtins where

import Agda.Compiler.MAlonzo.Compiler (ghcBackend)
import Agda.Compiler.JS.Compiler (jsBackend)
import Agda.Compiler.Backend (Backend)

builtinBackends :: [Backend]
builtinBackends = [ ghcBackend, jsBackend ]
