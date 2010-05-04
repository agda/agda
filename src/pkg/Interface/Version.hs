module Interface.Version where
-- FIXME: Proper Exports

import Agda.Version

--------------------------------------------------------------------------------

-- FIXME: Use Data.Version
versionString :: String
versionString = "Agda Package Registry Tool " ++ version
