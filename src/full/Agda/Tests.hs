
-- | Responsible for running all internal tests.
module Agda.Tests where

import Agda.Interaction.Highlighting.Emacs	 as InteEmac   (tests)
import Agda.Interaction.Highlighting.Generate as InteGene   (tests)
import Agda.Interaction.Highlighting.Precise	 as IntePrec   (tests)
import Agda.Interaction.Highlighting.Range	 as InteRang   (tests)
import Agda.Termination.Termination	         as TermTerm   (tests)
import Agda.Termination.CallGraph	         as TermCall   (tests)
import Agda.Termination.Lexicographic         as TermLex    (tests)
import Agda.Termination.Matrix	         as TermMatrix (tests)
import Agda.Termination.Semiring	         as TermRing   (tests)
import Agda.Termination.Utilities	         as TermUtil   (tests)
import Agda.TypeChecking.Serialise	         as TypeSeri   (tests)
import Agda.TypeChecking.Tests		 as TypeChck   (tests)
import Agda.Utils.Either	                 as UtilEith   (tests)
import Agda.Utils.FileName   	         as UtilFile   (tests)
import Agda.Utils.List	                 as UtilList   (tests)

runTests :: IO ()
runTests = do
    putStrLn "Tests in Agda.Interaction.Highlighting.Emacs"
    InteEmac.tests
    putStrLn "Tests in Agda.Interaction.Highlighting.Generate"
    InteGene.tests
    putStrLn "Tests in Agda.Interaction.Highlighting.Precise"
    IntePrec.tests
    putStrLn "Tests in Agda.Interaction.Highlighting.Range"
    InteRang.tests
    putStrLn "Tests in Agda.Termination.Termination"
    TermTerm.tests
    putStrLn "Tests in Agda.Termination.Utilities"
    TermUtil.tests
    putStrLn "Tests in Agda.Termination.Semiring"
    TermRing.tests
    putStrLn "Tests in Agda.Termination.Matrix"
    TermMatrix.tests
    putStrLn "Tests in Agda.Termination.Lexicographic"
    TermLex.tests
    putStrLn "Tests in Agda.Termination.CallGraph"
    TermCall.tests
    putStrLn "Tests in Agda.TypeChecking.Serialise"
    TypeSeri.tests
    putStrLn "Tests in Agda.TypeChecking.Tests"
    TypeChck.tests
    putStrLn "Tests in Agda.Utils.Either"
    UtilEith.tests
    putStrLn "Tests in Agda.Utils.FileName"
    UtilFile.tests
    putStrLn "Tests in Agda.Utils.List"
    UtilList.tests

