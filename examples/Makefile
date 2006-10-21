
TOP = ..

include $(TOP)/mk/paths.mk

default : test polydep aim4-bag ac minmax real

agda = $(FULL_OUT_DIR)/agda

test_files = Vec.agda Setoid.agda TT.agda \
			 AIM5/Hedberg/SET.agda AIM5/yoshiki/SET.agda \
             $(shell find Introduction -name '*.agda')
tests	   = $(patsubst %,%.test,$(test_files))

polydep : AIM5/PolyDep/Main.agda
	@echo "Testing $<... "
	@echo :q | $(agda) -iAIM5/PolyDep $<
	@echo "ok"

aim4-bag : AIM4/bag/Bag.agda
	@echo "Testing $<... "
	@echo :q | $(agda) -iAIM4/bag $<
	@echo "ok"

ac : tactics/ac/AC.agda
	@echo "Testing $<... "
	@echo :q | $(agda) -itactics/ac $<
	@echo "ok"

minmax : order/MinMax.agda
	@echo "Testing $<... "
	@echo :q | $(agda) -ilib -iorder $<
	@echo "ok"

real : lib/Data/Real/CReal.agda
	@echo "Testing $<... "
	@echo :q | $(agda) -ilib $<
	@echo "ok"

test : $(agda) $(tests)

$(tests) : %.test : %
	@echo -n "Testing $<... "
	@echo :q | $(agda) $<
	@echo "ok"
