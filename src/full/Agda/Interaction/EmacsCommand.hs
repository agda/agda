
------------------------------------------------------------------------
-- | Code for instructing Emacs to do things
------------------------------------------------------------------------

module Agda.Interaction.EmacsCommand
  ( Lisp(..)
  , response
  , putResponse
  , displayInfo
  , clearRunningInfo
  , displayRunningInfo
  ) where

-- import qualified Data.List as List

import Agda.Syntax.Common.Pretty
import Agda.Utils.String

-- | Simple Emacs Lisp expressions.

data Lisp a
  = A a
    -- ^ Atom.
  | Cons (Lisp a) (Lisp a)
    -- Cons cell.
  | L [Lisp a]
    -- ^ List.
  | Q (Lisp a)
    -- Quoted expression.
  deriving Eq

instance Pretty a => Pretty (Lisp a) where
  pretty (A a )     = pretty a
  pretty (Cons a b) = parens (pretty a <+> "." <+> pretty b)
  pretty (L xs)     = parens (hsep (map pretty xs))
  pretty (Q x)      = "'" <> pretty x

-- instance Show (Lisp String) where
--   showsPrec _ (A a)      = showString a
--   showsPrec p (Cons a b) = showString "(" . showsPrec p a . showString " . " .
--                                             showsPrec p b . showString ")"
--   showsPrec p (L xs)     = showString "(" . foldr (.) (showString ")")
--                                               (List.intersperse (showString " ")
--                                                  (map (showsPrec p) xs))
--   showsPrec p (Q x)      = showString "'" . showsPrec p x

-- | Formats a response command.
--
--   Replaces @'\n'@ with spaces to ensure that each command is a
--   single line.
response :: Lisp String -> String
response = (++ "\n") . map replaceNewLines . show . pretty
  where
  replaceNewLines '\n' = ' '
  replaceNewLines c    = c

-- | Writes a response command to standard output.

putResponse :: Lisp String -> IO ()
putResponse = putStr . response

-- | @displayInfo append header content@ displays @content@
-- (with header @header@) in some suitable way in the Agda information buffer.
-- If @append@ is @True@, then the content is appended to previous content
-- (if any), otherwise any previous content is deleted.

displayInfo :: Bool -> String -> String -> Lisp String
displayInfo append header content =
    L [ A "agda2-info-action"
      , A (quote header)
      , A (quote content)
      , A (if append then "t" else "nil")
      ]

------------------------------------------------------------------------
-- Running info

-- | Header to display in the Agda information buffer for "running info".

runningInfoHeader :: String
runningInfoHeader = "*Type-checking*"

-- | Clear the running info buffer.

clearRunningInfo :: Lisp String
clearRunningInfo =
    displayInfo False runningInfoHeader ""

-- | Display running information about what the type-checker is up to.

displayRunningInfo :: String -> Lisp String
displayRunningInfo s =
    displayInfo True runningInfoHeader s
