
TOP = ..

include $(TOP)/mk/paths.mk

default : test polydep aim4-bag ac minmax clowns real

agda = $(AGDA_BIN)

run_agda = $(agda) $(EXTRA_AGDA_FLAGS)

test_files = Vec.agda Setoid.agda TT.agda ISWIM.agda \
			 AIM5/Hedberg/SET.agda AIM5/yoshiki/SET.agda \
			 SimpleTypes.agda \
       $(shell find Introduction -name '*.agda')
tests	   = $(patsubst %,%.test,$(test_files))

polydep : AIM5/PolyDep/Main.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -iAIM5/PolyDep $<
	@echo "ok"

aim4-bag : AIM4/bag/Bag.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -iAIM4/bag $<
	@echo "ok"

ac : tactics/ac/AC.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -itactics/ac $<
	@echo "ok"

clowns : clowns/Clowns.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -ilib -iclowns $<
	@echo "ok"

minmax : order/MinMax.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -ilib -iorder $<
	@echo "ok"

real : lib/Data/Real/CReal.agda
	@echo "Testing $<... "
	@echo :q | $(run_agda) -ilib $<
	@echo "ok"

test : $(agda) $(tests)

$(tests) : %.test : %
	@echo -n "Testing $<... "
	@echo :q | $(run_agda) $<
	@echo "ok"

