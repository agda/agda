
TOP = ..
include $(TOP)/mk/paths.mk

include tests.mk

TAG			= $(shell echo `hostname -s`-`date +"%Y%m%d-%H.%M"`)
LOG_DIR = logs
PROC_INFO = $(shell which procinfo)
HOST_INFO = $(shell which hostinfo)

ifeq ($(HOST_INFO),)
ifeq ($(PROC_INFO),)
INFO = echo "No info"
else
INFO = $(PROC_INFO)
endif
else
INFO = $(HOST_INFO)
endif

logFiles = $(patsubst %,$(LOG_DIR)/$(TAG)/%,$(allTests))

all : $(logFiles)

$(LOG_DIR)/$(TAG)/% :
	@echo Running benchmark $*
	@mkdir -p $(LOG_DIR)/$(TAG)
	@$(AGDA_BIN) $($*) +RTS -s$@
	@echo "──────────────────────────────────────────────────────────────────" >> $@
	@$(INFO) >> $@

