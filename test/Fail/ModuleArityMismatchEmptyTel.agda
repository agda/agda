-- Andreas, 2015-12-01, test case to trigger error ModuleArityMismatch EmptyTel
module _ where

  module M where

  module M′ = M Set
