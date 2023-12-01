
TOP = ..

include $(TOP)/mk/paths.mk

# Keep the `default` prerequisites in alphabetic order please!
default : ac \
          aim4-bag \
          divmod \
          effects \
          hello \
          highlighting \
          html1 \
          html2 \
          library \
          malformed-interfaces \
          malonzo \
          minmax \
          other-examples \
          path \
          polydep \
          regexp-talk \
          relocatable-interfaces \
          simplelib \
          uptodate \
          view \

agda = $(AGDA_BIN)

run_agda = $(agda) -v0 --vim --ignore-interfaces --no-libraries

other_files = AIM5/Hedberg/SET.agda \
              AIM5/yoshiki/SET.agda \
              Binary.agda \
              DoNotation.agda \
              DTP08/conor/Talk.agda \
              DTP08/ulf/Talk.agda \
              ISWIM.agda \
              Lookup.agda \
              Miller/Pat.agda \
              Monad.agda  \
              ParenDepTac.agda \
              Setoid.agda \
              SimpleTypes.agda \
              syntax/Literate.lagda \
              Termination/Acc.agda \
              Termination/Mutual.agda \
              Termination/Nat.agda \
              Termination/Ord.agda \
              Termination/simplified-comb.agda \
              Termination/StreamEating.agda \
              Termination/StructuralOrder.agda \
              Termination/TerminationTwoConstructors.agda \
              Termination/Tuple.agda \
              TT.agda \
              Vec.agda

other_examples = $(patsubst %,%.other,$(other_files))

echo = $(shell which echo)
ifeq ("$(echo)","")
echo = echo
endif

.PHONY : polydep
polydep : AIM5/PolyDep/Main.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iAIM5/PolyDep $<
	@$(echo) "ok"

.PHONY : hello
hello : AIM6/HelloAgda/Everything.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iAIM6/HelloAgda $<
	@$(echo) "ok"

.PHONY : path
path : AIM6/Path/All.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iAIM6/Path $<
	@$(echo) "ok"

.PHONY : regexp-talk
regexp-talk : AIM6/RegExp/talk/Everything.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iAIM6/RegExp/talk $<
	@$(echo) "ok"

.PHONY : aim4-bag
aim4-bag : AIM4/bag/Bag.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iAIM4/bag $<
	@$(echo) "ok"

.PHONY : ac
ac : tactics/ac/AC.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -itactics/ac $<
	@$(echo) "ok"

.PHONY : effects
effects : sinatra/Example.agda
	@$(echo) "Testing $<..."
	@$(echo) :q | $(run_agda) -isinatra $<
	@$(echo) "ok"

.PHONY : minmax
minmax : order/MinMax.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -ilib -iorder $<
	@$(echo) "ok"

.PHONY : view
view : vfl/Typechecker.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -ivfl $<
	@$(echo) "ok"

.PHONY : simplelib
simplelib : simple-lib/TestLib.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -isimple-lib $<
	@$(echo) "ok"

.PHONY : library
library : lib/Test.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -ilib $<
	@$(echo) "ok"

.PHONY : divmod
divmod : arith/DivMod.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) -iarith -isimple-lib $<
	@$(echo) "ok"

.PHONY : intro
intro : Introduction/All.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) $<
	@$(echo) "ok"

.PHONY : highlighting
highlighting : syntax/highlighting/Test*agda
	@$(echo) "Testing $^... "
	@$(echo) :q | $(run_agda) --vim -isyntax/highlighting syntax/highlighting/Test2.agda
	@$(echo) :q | $(run_agda) --vim -isyntax/highlighting syntax/highlighting/Test3.lagda
	@$(echo) "ok"

.PHONY : malonzo
malonzo : compiler/main.agda
	@$(echo) "Testing the MAlonzo backend"
	@$(agda) --ignore-interfaces --compile --compile-dir=compiler -icompiler --no-libraries $<
	@./compiler/main
				# Compilation works also if the code has already been type
				# checked.
	@rm -rf compiler/main compiler/MAlonzo
	@$(agda) --compile --compile-dir=compiler -icompiler --no-libraries $<
	@./compiler/main
	@$(echo) "ok"

.PHONY : relocatable-interfaces
relocatable-interfaces : relocatable/originals/*.agda
	-@rm -rf relocatable/copies
	@$(echo) "Testing that interface files are relocatable"
	@$(agda) --ignore-interfaces -irelocatable/originals --no-libraries relocatable/originals/C.agda
	@cp -pR relocatable/originals relocatable/copies
	@echo "" >> relocatable/copies/B.agda
				# Type checking succeeds...
	@$(agda) -v2 -irelocatable/copies --no-libraries relocatable/copies/C.agda > relocatable/copies/output
	@cat relocatable/copies/output
				# ...and skips one of the modules (A).
	@[ `grep "^ *Checking A" relocatable/copies/output | wc -l` = 0 ]
	@[ `grep "^ *Checking B" relocatable/copies/output | wc -l` = 1 ]
	@[ `grep "^ *Checking C" relocatable/copies/output | wc -l` = 1 ]
	@rm -rf relocatable/copies

.PHONY : uptodate
uptodate : uptodate/*.agda
	@$(echo) "Testing that already imported modules are up-to-date" # despite having DOS line-endings
	@$(agda) --ignore-interfaces -iuptodate --no-libraries uptodate/A.agda > uptodate/output
	@cat uptodate/output
	@[ `grep "^ *Checking C" uptodate/output | wc -l` = 1 ]
	@rm -f uptodate/output

.PHONY : malformed-interfaces
malformed-interfaces : malformed/Empty.agda
	@$(echo) "Testing that Agda can handle at least some malformed interface files."
	@echo > malformed/Empty.agdai
	@$(agda) -imalformed --no-libraries malformed/Empty.agda
	-@openssl rand -out malformed/Empty.agdai 1024 2> /dev/null
	@$(agda) -imalformed --no-libraries malformed/Empty.agda
	@echo apa >> malformed/Empty.agdai
	@$(agda) -imalformed --no-libraries malformed/Empty.agda

.PHONY : html1
html1 : AIM6/RegExp/talk/Everything.agda
	@$(echo) "Testing HTML generation in the default directory"
	@$(run_agda) --html -iAIM6/RegExp/talk $<
	@[ -e html/Everything.html ]
	@rm -rf html
	@$(echo) "ok"

.PHONY : html2
html2 : AIM6/RegExp/talk/Everything.agda
	@$(echo) "Testing HTML generation in a particular directory"
	@$(run_agda) --html --html-dir=HTML -iAIM6/RegExp/talk $<
	@[ -e HTML/Everything.html ]
	@rm -rf HTML
	@$(echo) "ok"

.PHONY : other-examples
other-examples : $(other_examples)

$(other_examples) : %.other : %
	@$(echo) -n "Testing $<... "
	@$(echo) :q | $(run_agda) -i$(dir $<) $<
	@$(echo) "ok"

