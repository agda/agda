
TOP=../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk
include $(TOP)/mk/rules.mk

src_files = $(shell $(FIND) $(FULL_SRC_DIR) -name '*hs')

.uptodate : $(src_files)
	@rm $(AGDA_BIN)
	@touch .uptodate

$(AGDA_BIN) : Main.hs .uptodate
	$(RUNSETUP) build

