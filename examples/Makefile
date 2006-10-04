
TOP = ..

include $(TOP)/mk/paths.mk

default : test polydep

agda = $(FULL_OUT_DIR)/agda

test_files = Vec.agda bag.agda Setoid.agda TT.agda \
			 AIM5/Hedberg/SET.agda AIM5/yoshiki/SET.agda \
             $(shell find Introduction -name '*.agda')
tests	   = $(patsubst %,%.test,$(test_files))

polydep : AIM5/PolyDep/Main.agda
	@echo "Testing $<... "
	@echo :q | $(agda) -iAIM5/PolyDep $<
	@echo "ok"

test : $(agda) $(tests)

$(tests) : %.test : %
	@echo -n "Checking $<... "
	@echo :q | $(agda) $<
	@echo "ok"
