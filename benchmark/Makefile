TOP=../

include $(TOP)/mk/paths.mk

include tests.mk

# Note: The use of ":=" rather than "=" ensures that the right-hand
# side of TAG is not expanded multiple times.
TAG := $(shell echo `date +"%Y%m%d-%H.%M"`-`hostname -s`)
LOG_DIR = logs
PROC_INFO := $(shell which procinfo)
HOST_INFO := $(shell which hostinfo)

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

verbose = -v0 --profile=constraints --profile=metas

.PHONY: all
all : clean $(logDir) $(logFiles)

# If an error is encountered, then the logs are not removed.
.PHONY: without-creating-logs
without-creating-logs : all
	@$(RUNGHC) Benchmark.hs $(TAG)
	rm -r $(logDir)

.PHONY: summary
summary :
	@$(RUNGHC) Benchmark.hs

$(logDir) :
	@mkdir -p $@

$(LOG_DIR)/$(TAG)/% :
	@echo Running benchmark $*
	@$(AGDA_BIN) $(verbose) --no-default-libraries $($*) +RTS -slogs/.tmp > $@
	@cat logs/.tmp >> $@
	@rm logs/.tmp
	@echo "──────────────────────────────────────────────────────────────────" >> $@
	@$(INFO) >> $@

.PHONY: clean
clean :
	@find . -type f -name '*.agdai' -delete

.PHONY: debug
debug :
	@echo "INFO     = $(INFO)"
	@echo "LOG_DIR  = $(LOG_DIR)"
	@echo "TAG      = $(TAG)"
	@echo "verbose  = $(verbose)"
	@echo "logDir   = $(logDir)"
	@echo "logFiles = $(logFiles)"

# EOF
