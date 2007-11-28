
TOP=../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk
include $(TOP)/mk/rules.mk

src_files = $(shell $(FIND) $(FULL_SRC_DIR) -name '*hs') \
						$(shell $(FIND) $(FULL_SRC_DIR) -name '*.x') \
						$(shell $(FIND) $(FULL_SRC_DIR) -name '*.y')

AGDA_BIN_P = dist/build/agda/agda_p

.uptodate : $(src_files)
	@rm -f $(AGDA_BIN) $(AGDA_BIN_P)
	@touch .uptodate

$(AGDA_BIN) : Main.hs .uptodate
	$(RUNSETUP) build

prof : $(AGDA_BIN_P)

$(AGDA_BIN_P) : Main.hs .uptodate
	$(GHC) --make Main.hs -O -prof -auto-all -o $@

