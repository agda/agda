-- | The list of data files Agda uses.
--
-- Because of TemplateHaskell state restrictions, this cannot be define in ''Agda.Setup''.

module Agda.Setup.DataFiles where

-- | A data file path relative to the project root.

dataPath :: FilePath -> FilePath
dataPath = ("src/data/" ++)
-- Do we need to bother with </> for Windows?
-- dataPath f = "src" </> "data" </> f

-- | Agda's embedded data files.

-- KEEP IN SYNC with the list in Agda.cabal under extra-source-files!
dataFiles :: [FilePath]
dataFiles =
  map ((emacsModeDir ++ "/") ++) emacsLispFiles ++
  -- N.B.: agda2-mode-pkg.el is not part of emacsLispFiles as it need not be compiled.
  [ "emacs-mode/agda2-mode-pkg.el"
  , "html/Agda.css"
  , "html/highlight-hover.js"
  , "JS/agda-rts.mjs"
  , "JS/agda-rts.js"
  , "JS/agda-rts.amd.js"
  , "latex/agda.sty"
  , "latex/postprocess-latex.pl"
  , "lib/prim/agda-builtins.agda-lib"
  , "lib/prim/Agda/Builtin/Bool.agda"
  , "lib/prim/Agda/Builtin/Char.agda"
  , "lib/prim/Agda/Builtin/Char/Properties.agda"
  , "lib/prim/Agda/Builtin/Coinduction.agda"
  , "lib/prim/Agda/Builtin/Cubical/Path.agda"
  , "lib/prim/Agda/Builtin/Cubical/Sub.agda"
  , "lib/prim/Agda/Builtin/Cubical/Glue.agda"
  , "lib/prim/Agda/Builtin/Cubical/Equiv.agda"
  , "lib/prim/Agda/Builtin/Cubical/HCompU.agda"
  , "lib/prim/Agda/Builtin/Equality.agda"
  , "lib/prim/Agda/Builtin/Equality/Erase.agda"
  , "lib/prim/Agda/Builtin/Equality/Rewrite.agda"
  , "lib/prim/Agda/Builtin/Float.agda"
  , "lib/prim/Agda/Builtin/Float/Properties.agda"
  , "lib/prim/Agda/Builtin/FromNat.agda"
  , "lib/prim/Agda/Builtin/FromNeg.agda"
  , "lib/prim/Agda/Builtin/FromString.agda"
  , "lib/prim/Agda/Builtin/IO.agda"
  , "lib/prim/Agda/Builtin/Int.agda"
  , "lib/prim/Agda/Builtin/List.agda"
  , "lib/prim/Agda/Builtin/Maybe.agda"
  , "lib/prim/Agda/Builtin/Nat.agda"
  , "lib/prim/Agda/Builtin/Reflection.agda"
  , "lib/prim/Agda/Builtin/Reflection/External.agda"
  , "lib/prim/Agda/Builtin/Reflection/Properties.agda"
  , "lib/prim/Agda/Builtin/Sigma.agda"
  , "lib/prim/Agda/Builtin/Size.agda"
  , "lib/prim/Agda/Builtin/Strict.agda"
  , "lib/prim/Agda/Builtin/String.agda"
  , "lib/prim/Agda/Builtin/String/Properties.agda"
  , "lib/prim/Agda/Builtin/TrustMe.agda"
  , "lib/prim/Agda/Builtin/Unit.agda"
  , "lib/prim/Agda/Builtin/Word.agda"
  , "lib/prim/Agda/Builtin/Word/Properties.agda"
  , "lib/prim/Agda/Primitive.agda"
  , "lib/prim/Agda/Primitive/Cubical.agda"
  , "MAlonzo/src/MAlonzo/RTE.hs"
  , "MAlonzo/src/MAlonzo/RTE/Float.hs"
  ]

-- | The subdirectory in the Agda data directory containing the emacs mode.

emacsModeDir :: FilePath
emacsModeDir = "emacs-mode"

-- | The Agda mode's Emacs Lisp files, given in the order in which
-- they should be compiled.

emacsLispFiles :: [FilePath]
emacsLispFiles =
  [ "agda2-abbrevs.el"
  , "annotation.el"
  , "agda2-queue.el"
  , "eri.el"
  , "agda2.el"
  , "agda-input.el"
  , "agda2-highlight.el"
  , "agda2-mode.el"
  ]
  -- N.B.: We also ship agda2-mode-pkg.el for melpa,
  -- but this is not part of the emacs mode and need not be compiled.
