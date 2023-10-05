
# Tests in categories
catBenchmark = categories/$1.agda -icategories --ignore-interfaces +RTS -K32M -RTS
cat			 = $(call catBenchmark,Categories)
prim		 = $(call catBenchmark,Primitive)
catTests = cat prim

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
monadpostulate = monad/MonadPostulates.agda -i../std-lib/src -imonad
monadTests = monad monadpostulate

#misc
misc				 = misc/$1.agda -imisc --ignore-interfaces
functor			 = $(call misc,Functor)
latemeta		 = $(call misc,LateMetaVariableInstantiation)
polyfunctor  = $(call misc,UniversePolymorphicFunctor)
patternmatch = $(call misc,Coverage)
instanceargs = $(call misc,InstanceArgs)
miscTests		 = functor latemeta polyfunctor patternmatch instanceargs

#proj
proj = proj/$1.agda -iproj --ignore-interfaces
record = $(call proj,Record)
data   = $(call proj,Data)
nested = $(call proj,Nested)
projTests = record data nested

#std-lib
stdlib = std-lib/$1.agda -istd-lib -i../std-lib/src
any = $(call stdlib,Any)
stdlibTests =

# All tests
allTests = $(catTests) $(acTests) $(syntaxTests) $(cwfTests) $(monadTests) $(miscTests) $(projTests) $(stdlibTests)
