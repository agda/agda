#define __IMPOSSIBLE__ (throwImpossible (Impossible __FILE__ __LINE__))
#define __IMPOSSIBLE_TERM__ (impossibleTerm __FILE__ __LINE__)

#define __IMPOSSIBLE_VERBOSE__ (\ s -> do { reportSLn "impossible" 10 s ; __IMPOSSIBLE__ })

#define __UNREACHABLE__ (throwImpossible (Unreachable __FILE__ __LINE__))
#define __CRASH_WHEN__ (\ k n -> whenExactVerbosity k n __UNREACHABLE__)

#define __DUMMY_TERM__  (dummyTerm  __FILE__ __LINE__)
#define __DUMMY_TYPE__  (dummyType  __FILE__ __LINE__)
#define __DUMMY_SORT__  (dummySort  __FILE__ __LINE__)
#define __DUMMY_LEVEL__ (dummyLevel __FILE__ __LINE__)
#define __DUMMY_DOM__   (dummyDom   __FILE__ __LINE__)
