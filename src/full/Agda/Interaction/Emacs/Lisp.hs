-- | Abstract elisp syntax.

module Agda.Interaction.Emacs.Lisp
  ( Lisp(..)
  , response
  , putResponse
  ) where

import Agda.Syntax.Common.Pretty

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
response = (++ "\n") . map replaceNewLines . prettyShow
  where
  replaceNewLines '\n' = ' '
  replaceNewLines c    = c

-- | Writes a response command to standard output.

putResponse :: Lisp String -> IO ()
putResponse = putStr . response
