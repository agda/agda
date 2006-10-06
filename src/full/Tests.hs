
-- | Responsible for running all internal tests.
module Tests where

import Termination.CallGraph	 as TermCall   (tests)
import Termination.Lexicographic as TermLex    (tests)
import Termination.Matrix	 as TermMatrix (tests)
import Termination.Semiring	 as TermRing   (tests)
import Termination.TestHelpers	 as TermHelp   (tests)
import Termination.Utilities	 as TermUtil   (tests)

runTests :: IO ()
runTests = do
    putStrLn "Tests in Termination.Utilities"
    TermUtil.tests
    putStrLn "Tests in Termination.TestHelpers"
    TermHelp.tests
    putStrLn "Tests in Termination.Semiring"
    TermRing.tests
    putStrLn "Tests in Termination.Matrix"
    TermMatrix.tests
    putStrLn "Tests in Termination.Lexicographic"
    TermLex.tests
    putStrLn "Tests in Termination.CallGraph"
    TermCall.tests

