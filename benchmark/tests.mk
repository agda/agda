
# Tests in categories
cat			 = categories/Categories.agda -icategories --ignore-interfaces +RTS -K32M -RTS
catTests = cat

# Tests in ac
ac1			= ac/AC.agda --ignore-interfaces -iac
ac2			= ac/Example.agda --ignore-interfaces -iac
ac3			= ac/Example.agda -iac
acTests = ac1 ac2 ac3

# Syntacticosmos
syntax1	= Syntacticosmos/UntypedLambda.agda --ignore-interfaces -iSyntacticosmos +RTS -K32M
syntax2	= Syntacticosmos/UntypedLambda.agda -iSyntacticosmos +RTS -K32M
syntaxTests = syntax1 syntax2

# cwf
cwf = cwf/CwF.agda --ignore-interfaces -icwf
cwfTests = cwf

# Parsing monad
monad = monad/Monad.agda -i../std-lib/src -imonad
monadTests = monad

#misc
misc = misc/$1.agda -imisc --ignore-interfaces
functor = $(call misc,Functor)
latemeta = $(call misc,LateMetaVariableInstantiation)
polyfunctor = $(call misc,UniversePolymorphicFunctor)
miscTests = functor latemeta polyfunctor

# All tests
allTests = $(catTests) $(acTests) $(syntaxTests) $(cwfTests) $(monadTests) $(miscTests)

