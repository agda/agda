open import Agda.Builtin.IO
open import Agda.Builtin.List
open import Agda.Builtin.Size
open import Agda.Builtin.String

record Thunk (F : Size → Set) (i : Size) : Set where
  coinductive
  field force : {j : Size< i} → F j
open Thunk public

FilePath = String

-- A directory tree is rooted in the current directory; it comprises:
-- * a list of files in the current directory
-- * an IO action returning a list of subdirectory trees

-- This definition does not typecheck if IO is not marked as strictly positive
data DirectoryTree (i : Size) : Set where
  _:<_ : List FilePath → IO (List (Thunk DirectoryTree i)) →
         DirectoryTree i
