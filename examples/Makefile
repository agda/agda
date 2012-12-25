
TOP = ..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk

default : test polydep hello path regexp-talk aim4-bag ac effects minmax real view simplelib lib divmod highlighting malonzo relocatable-interfaces malformed-interfaces term1 term2 term3 html1 html2 epic

agda = $(AGDA_BIN)

run_agda = $(agda) -v0 --vim $(AGDA_TEST_FLAGS)

test_files = Vec.agda Lookup.agda Binary.agda Setoid.agda \
			 TT.agda ISWIM.agda ParenDepTac.agda \
			 AIM5/Hedberg/SET.agda AIM5/yoshiki/SET.agda \
			 SimpleTypes.agda Monad.agda Miller/Pat.agda \
       syntax/Literate.lagda Termination/StreamEating.agda \
	instance-arguments/01-arguments.agda \
	instance-arguments/02-classes-indep.agda \
	instance-arguments/04-equality.agda \
	instance-arguments/06-listEquality.agda \
	instance-arguments/07-subclasses.agda \
	instance-arguments/08-higherOrder.agda \
	instance-arguments/13-implicitProofObligations.agda \
	instance-arguments/14-implicitConfigurations.agda
# the other instance-arguments examples use the standard library,
# seemingly no way to include it during test run...
tests	   = $(patsubst %,%.test,$(test_files))

echo = $(shell which echo)
ifeq ("$(echo)","")
echo = echo
endif

term1 : Termination/Mutual.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iTermination $<
	@$(echo) "ok"

term2 : Termination/StructuralOrder.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iTermination $<
	@$(echo) "ok"

term3 : Termination/Tuple.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iTermination $<
	@$(echo) "ok"

polydep : AIM5/PolyDep/Main.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iAIM5/PolyDep $<
	@$(echo) "ok"

hello : AIM6/HelloAgda/Everything.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iAIM6/HelloAgda $<
	@$(echo) "ok"

path : AIM6/Path/All.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iAIM6/Path $<
	@$(echo) "ok"

regexp-talk : AIM6/RegExp/talk/Everything.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iAIM6/RegExp/talk $<
	@$(echo) "ok"

aim4-bag : AIM4/bag/Bag.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iAIM4/bag $<
	@$(echo) "ok"

ac : tactics/ac/AC.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -itactics/ac $<
	@$(echo) "ok"

effects : sinatra/Example.agda
	@$(echo) "Testing $<..."
	@$(echo) :q | $(run_agda) -isinatra $<
	@$(echo) "ok"

minmax : order/MinMax.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -ilib -iorder $<
	@$(echo) "ok"

real : lib/Data/Real/CReal.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -ilib $<
	@$(echo) "ok"

view : vfl/Typechecker.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -ivfl $<
	@$(echo) "ok"

simplelib : simple-lib/TestLib.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -isimple-lib $<
	@$(echo) "ok"

lib : lib/Test.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -ilib $<
	@$(echo) "ok"

divmod : arith/DivMod.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iarith -isimple-lib $<
	@$(echo) "ok"

intro : Introduction/All.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) $<
	@$(echo) "ok"

highlighting : syntax/highlighting/Test*agda
	@$(echo) "Testing $^... "
	@$(echo) :q | $(run_agda) --vim -isyntax/highlighting syntax/highlighting/Test2.agda
	@$(echo) :q | $(run_agda) --vim -isyntax/highlighting syntax/highlighting/Test3.lagda
	@$(echo) "ok"

malonzo : compiler/main.agda
	@$(echo) "Testing the MAlonzo backend"
	@$(agda) --ignore-interfaces --compile --compile-dir=compiler -icompiler $<
	@./compiler/main
        # Compilation works also if the code has already been type
        # checked.
	@rm -rf compiler/main compiler/MAlonzo
	@$(agda) --compile --compile-dir=compiler -icompiler $<
	@./compiler/main
	@$(echo) "ok"

epic : compiler/main.agda
	@$(echo) "Testing the Epic backend"
	@$(agda) --ignore-interfaces --epic --compile-dir=compiler -icompiler $<
	@./compiler/main
        # Compilation works also if the code has already been type
        # checked.
	@rm -rf compiler/main compiler/Epic
	@$(agda) --epic --compile-dir=compiler -icompiler $<
	@./compiler/main
	@$(echo) "ok"

relocatable-interfaces : relocatable/originals/*.agda
	-@rm -rf relocatable/copies
	@$(echo) "Testing that interface files are relocatable"
	@$(agda) --ignore-interfaces -irelocatable/originals relocatable/originals/C.agda
	@cp -pR relocatable/originals relocatable/copies
	@sleep 1
	@touch relocatable/copies/B.agda
	@sleep 2
        # Type checking succeeds...
	@$(agda) -irelocatable/copies relocatable/copies/C.agda > relocatable/copies/output
	@cat relocatable/copies/output
        # ...and skips one of the modules (A).
	@[ `grep "^ *Skipping" relocatable/copies/output | wc -l` = 1 ]
	@rm -rf relocatable/copies

malformed-interfaces : malformed/Empty.agda
	@$(echo) "Testing that Agda can handle at least some malformed interface files."
	@echo > malformed/Empty.agdai
	@$(agda) -imalformed malformed/Empty.agda
	-@openssl rand -out malformed/Empty.agdai 1024 2> /dev/null
	@$(agda) -imalformed malformed/Empty.agda
	@echo apa >> malformed/Empty.agdai
	@$(agda) -imalformed malformed/Empty.agda

html1 : AIM6/RegExp/talk/Everything.agda
	@$(echo) "Testing HTML generation in the default directory"
	@$(run_agda) --html -iAIM6/RegExp/talk $<
	@[ -e html/Everything.html ]
	@rm -rf html
	@$(echo) "ok"

html2 : AIM6/RegExp/talk/Everything.agda
	@$(echo) "Testing HTML generation in a particular directory"
	@$(run_agda) --html --html-dir=HTML -iAIM6/RegExp/talk $<
	@[ -e HTML/Everything.html ]
	@rm -rf HTML
	@$(echo) "ok"

test : $(tests)

$(tests) : %.test : %
	@$(echo) -n "Testing $<... "
	@$(echo) :q | $(run_agda) -i$(dir $<) $<
	@$(echo) "ok"

