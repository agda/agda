
# Tests in categories
cat			 = categories/Categories.agda --ignore-interfaces +RTS -K32M -RTS
catTests = cat

# Tests in ac
ac1			= ac/AC.agda --ignore-interfaces -iac -v0
ac2			= ac/Example.agda --ignore-interfaces -iac -v0
ac3			= ac/Example.agda -iac -v0
acTests = ac1 ac2 ac3

# Syntacticosmos
syntax1	= Syntacticosmos/UntypedLambda.agda --ignore-interfaces -iSyntacticosmos -v0 +RTS -K32M
syntax2	= Syntacticosmos/UntypedLambda.agda -iSyntacticosmos -v0 +RTS -K32M
syntaxTests = syntax1 syntax2

# cwf
cwf = cwf/CwF.agda --ignore-interfaces -icwf -v0
cwfTests = cwf

# Parsing monad
monad = monad/Monad.agda -i../std-lib
monadTests = monad

# All tests
allTests = $(catTests) $(acTests) $(syntaxTests) $(cwfTests) $(monadTests)

