
-- | Responsible for running all internal tests.
module Tests where

import Interaction.Highlighting.Emacs	 as InteEmac   (tests)
import Interaction.Highlighting.Generate as InteGene   (tests)
import Interaction.Highlighting.Precise	 as IntePrec   (tests)
import Termination.CallGraph	         as TermCall   (tests)
import Termination.Lexicographic         as TermLex    (tests)
import Termination.Matrix	         as TermMatrix (tests)
import Termination.Semiring	         as TermRing   (tests)
import Termination.Termination	         as TermTerm   (tests)
import Termination.Utilities	         as TermUtil   (tests)
import Utils.FileName   	         as UtilFile   (tests)
import Utils.List	                 as UtilList   (tests)
import Utils.TestHelpers	         as UtilTest   (tests)

runTests :: IO ()
runTests = do
    putStrLn "Tests in Interaction.Highlighting.Emacs"
    InteEmac.tests
    putStrLn "Tests in Interaction.Highlighting.Generate"
    InteGene.tests
    putStrLn "Tests in Interaction.Highlighting.Precise"
    IntePrec.tests
    putStrLn "Tests in Termination.Utilities"
    TermUtil.tests
    putStrLn "Tests in Termination.Semiring"
    TermRing.tests
    putStrLn "Tests in Termination.Termination"
    TermTerm.tests
    putStrLn "Tests in Termination.Matrix"
    TermMatrix.tests
    putStrLn "Tests in Termination.Lexicographic"
    TermLex.tests
    putStrLn "Tests in Termination.CallGraph"
    TermCall.tests
    putStrLn "Tests in Utils.FileName"
    UtilFile.tests
    putStrLn "Tests in Utils.List"
    UtilList.tests
    putStrLn "Tests in Utils.TestHelpers"
    UtilTest.tests

