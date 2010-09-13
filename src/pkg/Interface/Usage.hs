{-# LANGUAGE OverloadedStrings #-}

module Interface.Usage where
-- FIXME: Proper Exports

import Control.Monad.Identity
import qualified Data.ByteString.Char8
  as BS
import Utils

--------------------------------------------------------------------------------

usageHeader :: BS.ByteString -> BS.ByteString
usageHeader = runIdentity
            . substitute usageMsg progRegEx
            . (const . return)
  where
    progRegEx = "\\$p"
    usageMsg  = BS.concat
     [ "Usage:\n"
     , "  $p describe {pkg}\n"
     , "    Give the registered description for the specified package. The\n"
     , "    description is returned in precisely the syntax required by $p\n"
     , "    register.\n"
     , "\n"
     , "  $p dump\n"
     , "    Dump the registered description for every package.  This is like\n"
     , "    \"$p describe '*'\", except that it is intended to be used\n"
     , "    by tools that parse the results, rather than humans.\n"
     , "\n"
     , "  $p expose {pkg-id}\n"
     , "    Expose the specified package.\n"
     , "\n"
     , "  $p hide {pkg-id}\n"
     , "    Hide the specified package.\n"
     , "\n"
     , "  $p list [pkg]\n"
     , "    List registered packages in the database.\n"
     , "\n"
     , "  $p register {filename | -}\n"
     , "    Register the package using the specified installed package\n"
     , "    description. The syntax for the latter is given in the $p\n"
     , "    documentation.\n"
     , "\n"
     , "  $p update {filename | -}\n"
     , "    Register the package, overwriting any other package with the\n"
     , "    same name.\n"
     , "\n"
     , "  $p unregister {pkg-id}\n"
     , "    Unregister the specified package.\n"
     , "\n"
     , " The following optional flags are also accepted:\n"
     ]
