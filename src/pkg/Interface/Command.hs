module Interface.Command
  ( module Interface.Command.Dump
  , module Interface.Command.List
  , module Interface.Command.Register
  , module Interface.Command.Visibility
  , Cmd ) where

import Interface.Command.Dump
import Interface.Command.List
import Interface.Command.Register
import Interface.Command.Visibility

--------------------------------------------------------------------------------

type Cmd = String
