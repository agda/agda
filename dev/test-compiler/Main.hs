
import Compiler.Tests (tests)
import AgdaDisabledTests (runTests)

main :: IO ()
main = runTests =<< tests
