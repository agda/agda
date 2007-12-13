
TOP = ..
include $(TOP)/mk/paths.mk

include tests.mk

SUFFIX = $(shell echo `hostname -s`-`date +"%Y%m%d-%H.%M"`.log)
LOG_DIR = logs

logFiles = $(patsubst %,$(LOG_DIR)/%-$(SUFFIX),$(allTests))

all : $(logFiles)

$(LOG_DIR)/%-$(SUFFIX) :
	@echo Running benchmark $*
	@$(AGDA_BIN) $($*) +RTS -s$@
	@echo "──────────────────────────────────────────────────────────────────" >> $@
	@hostinfo >> $@

