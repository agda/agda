
TOP = ..
include $(TOP)/mk/paths.mk

include tests.mk

TAG			= $(shell echo `date +"%Y%m%d-%H.%M"`-`hostname -s`)
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

logDir = $(LOG_DIR)/$(TAG)
logFiles = $(patsubst %,$(logDir)/%,$(allTests))

all : $(logDir) $(logFiles)

$(logDir) :
	@mkdir -p $@

$(LOG_DIR)/$(TAG)/% :
	@echo Running benchmark $*
	@$(AGDA_BIN) $($*) +RTS -s$@
	@echo "──────────────────────────────────────────────────────────────────" >> $@
	@$(INFO) >> $@

