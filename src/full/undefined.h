#define __IMPOSSIBLE__ (throwImpossible (withFileAndLine Impossible))
#define __IMPOSSIBLE_TERM__ (withFileAndLine impossibleTerm)

#define __IMPOSSIBLE_VERBOSE__ (\ s -> do { reportSLn "impossible" 10 s ; __IMPOSSIBLE__ })

#define __UNREACHABLE__ (throwImpossible (withFileAndLine Unreachable))
#define __CRASH_WHEN__ (\ k n -> whenExactVerbosity k n __UNREACHABLE__)

#define __DUMMY_TERM__  (withFileAndLine dummyTerm)
#define __DUMMY_TYPE__  (withFileAndLine dummyType)
#define __DUMMY_SORT__  (withFileAndLine dummySort)
#define __DUMMY_LEVEL__ (withFileAndLine dummyLevel)
#define __DUMMY_DOM__   (withFileAndLine dummyDom)
