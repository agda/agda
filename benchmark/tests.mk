
# Tests in categories
cat			 = categories/Categories.agda --ignore-interfaces +RTS -K32M -RTS
catTests = cat

# Tests in ac
ac1			= ac/AC.agda --ignore-interfaces -iac -v0
ac2			= ac/Example.agda --ignore-interfaces -iac -v0
ac3			= ac/Example.agda -iac -v0
acTests = ac1 ac2 ac3

# All tests
allTests = $(catTests) $(acTests)

