#define __IMPOSSIBLE__ (throwImpossible (Impossible __FILE__ __LINE__))

#define __EMACSMODE__ (error $ __FILE__ ++ ":" ++ show __LINE__ ++ ": I'm not touching this code!  /Ulf")

