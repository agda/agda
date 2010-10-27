{-# OPTIONS #-}
module PluginType  (
  -- * Type declarations
  Plugin (..),
  -- * Class declarations

  -- * Function types

  -- * Exported modules

  -- * Notes
)

where
import Position(Position)
import PPrint
import Utilities (t)

data Plugin a tc = Plugin {
                     pluginPos  :: Position,
                     pluginName :: String,
                     pluginOpts :: String,
                     pluginArgs :: [a],
		     pluginTransClass :: tc
                   }
  deriving (Eq, Show,Ord)


instance (PPrint a, PPrint tc) => PPrint (Plugin a tc) where
      pPrint d _ (Plugin pos name opts es tc)
        = text "\"" ~. t name ~. text "\"" ~. separate (t opts : map (pPrint d 10) es)
          -- separate (t name:t opts : map (pPrint d 10) es)
