module Interface.Options where
-- FIXME: Proper Exports

-- Standard Library Imports
import System.Console.GetOpt

--------------------------------------------------------------------------------

data Opt
  = OptDBCustom FilePath
  | OptDBGlobal
  | OptDBUser
  | OptHelp
  | OptVersion
    deriving (Eq)

allOpts :: [OptDescr Opt]
allOpts =
  [ Option []    ["global"]       (NoArg  OptDBGlobal)
      "Operate on the global package database."

  , Option ['f'] ["package-conf"] (ReqArg OptDBCustom "FILE")
      "Operate on a specific package database."

  , Option []    ["user"]         (NoArg  OptDBUser)
      "Operate on the current user's package database."

  , Option ['V'] ["version"]      (NoArg  OptVersion)
      "Output version information and exit."

  , Option ['?'] ["help"]         (NoArg  OptHelp)
      "Display this help and exit."
  ]
