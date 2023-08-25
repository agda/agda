-- | Types related to warnings raised by Agda.

module Agda.TypeChecking.Monad.Base.Warning where

import           GHC.Generics               (Generic)

import           Agda.Syntax.Abstract.Name
import           Agda.Syntax.Position       (Range)
import qualified Agda.Syntax.Concrete.Name  as C

data RecordFieldWarning
  = DuplicateFields [(C.Name, Range)]
      -- ^ Each redundant field comes with a range of associated dead code.
  | TooManyFields QName [C.Name] [(C.Name, Range)]
      -- ^ Record type, fields not supplied by user, non-fields but supplied.
      --   The redundant fields come with a range of associated dead code.
  deriving (Show, Generic)
