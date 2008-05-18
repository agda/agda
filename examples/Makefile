
TOP = ..

include $(TOP)/mk/paths.mk

default : test polydep hello path regexp-talk aim4-bag ac effects minmax real view simplelib lib divmod

agda = $(AGDA_BIN)

run_agda = $(agda) --vim --emacs $(EXTRA_AGDA_FLAGS)

test_files = Vec.agda Lookup.agda Binary.agda Setoid.agda \
			 TT.agda ISWIM.agda ParenDepTac.agda \
			 AIM5/Hedberg/SET.agda AIM5/yoshiki/SET.agda \
			 SimpleTypes.agda Monad.agda Miller/Pat.agda \
                         syntax/Literate.lagda \
       $(shell find Introduction -name '*.agda')
tests	   = $(patsubst %,%.test,$(test_files))

polydep : AIM5/PolyDep/Main.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -iAIM5/PolyDep $<
	@echo "ok"

hello : AIM6/HelloAgda/Everything.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -iAIM6/HelloAgda $<
	@echo "ok"

path : AIM6/Path/All.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -iAIM6/Path $<
	@echo "ok"

regexp-talk : AIM6/RegExp/talk/Everything.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -iAIM6/RegExp/talk $<
	@echo "ok"

aim4-bag : AIM4/bag/Bag.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -iAIM4/bag $<
	@echo "ok"

ac : tactics/ac/AC.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -itactics/ac $<
	@echo "ok"

effects : sinatra/Example.agda
	@echo "Testing $<..."
	@echo :q | $(run_agda) -isinatra $<
	@echo "ok"

minmax : order/MinMax.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -ilib -iorder $<
	@echo "ok"

real : lib/Data/Real/CReal.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -ilib $<
	@echo "ok"

view : vfl/Typechecker.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) $<
	@echo "ok"

simplelib : simple-lib/TestLib.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -isimple-lib $<
	@echo "ok"

lib : lib/Test.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -ilib $<
	@echo "ok"

divmod : arith/DivMod.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -isimple-lib $<
	@echo "ok"

highlighting : syntax/highlighting/All.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -isyntax/highlighting $<
	@echo "ok"

test : $(tests)

$(tests) : %.test : %
	@echo -n "Testing $<... "
	@echo :q | $(run_agda) $<
	@echo "ok"

