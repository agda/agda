#define __IMPOSSIBLE__ (throwImpossible (Impossible __FILE__ __LINE__))
#define __IMPOSSIBLE_TERM__ (impossibleTerm __FILE__ __LINE__)

#define __UNREACHABLE__ (throwImpossible (Unreachable __FILE__ __LINE__))
#define __CRASH_WHEN__ (\ k n -> whenExactVerbosity k n __UNREACHABLE__)
