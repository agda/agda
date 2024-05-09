module Issue7250.B where

import Issue7250.A
open module A′ = Issue7250.A public

-- module One′ = One
-- open One′ public
-- open One
-- ^ no combination helps
