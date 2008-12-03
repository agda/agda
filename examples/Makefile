
TOP = ..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk

default : test polydep hello path regexp-talk aim4-bag ac effects minmax real view simplelib lib divmod highlighting compiler term1 term2 term3

agda = $(AGDA_BIN)

run_agda = $(agda) --vim --emacs $(AGDA_TEST_FLAGS)

test_files = Vec.agda Lookup.agda Binary.agda Setoid.agda \
			 TT.agda ISWIM.agda ParenDepTac.agda \
			 AIM5/Hedberg/SET.agda AIM5/yoshiki/SET.agda \
			 SimpleTypes.agda Monad.agda Miller/Pat.agda \
       syntax/Literate.lagda StreamEating.agda \
       $(shell find Introduction -name '*.agda')
tests	   = $(patsubst %,%.test,$(test_files))

echo = $(shell which echo)
ifeq ("$(echo)","")
echo = echo
endif

term1 : Termination/Mutual.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) $<
	@$(echo) "ok"

term2 : Termination/StructuralOrder.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) $<
	@$(echo) "ok"

term3 : Termination/Tuple.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) $<
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
	@$(echo) :q | $(run_agda) $<
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
	@$(echo) :q | $(run_agda) -isimple-lib $<
	@$(echo) "ok"

highlighting : syntax/highlighting/Test*agda
	@$(echo) "Testing $^... "
	@$(echo) :q | $(run_agda) --emacs --vim -isyntax/highlighting syntax/highlighting/Test2.agda
	@$(echo) :q | $(run_agda) --emacs --vim -isyntax/highlighting syntax/highlighting/Test3.lagda
	@$(echo) "ok"

compiler : MAlonzo/main.agda
	@$(echo) "Testing $<... "
	@$(echo) :q | $(run_agda) --compile --malonzodir=MAlonzo -iMAlonzo $<
	@./main
	@$(echo) "ok"

test : $(tests)

$(tests) : %.test : %
	@$(echo) -n "Testing $<... "
	@$(echo) :q | $(run_agda) $<
	@$(echo) "ok"

