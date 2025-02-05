# Makefile for Sphinx documentation
###########################################################################

# You can set these variables from the command line.
SPHINXOPTS    = -E -W --keep-going
SPHINXBUILD   = sphinx-build
SOURCEDIR     = .
BUILDDIR      = _build

# The Python virtual environment should be below the current directory
# lest sphinx gets confused and tries to build documentation
# for the Python code in the virtual environment directories.
VENV          = ../../.python-sphinx-virtualenv
VENV_ACTIVATE = $(VENV)/bin/activate

# Put it first so that "make" without argument is like "make help".
.PHONY: help
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

# Suppress warning: make: Circular Makefile <- Makefile dependency dropped.
.PHONY: Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile $(VENV_ACTIVATE)
	@(. $(VENV_ACTIVATE) && pip install -r requirements.txt && $(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O))


# Python virtual environment
###########################################################################

# Create a Python virtual environment.
# Note: use '.' instead 'source' for sh compatibility.
$(VENV_ACTIVATE):
	python3 -m venv $(VENV)
	(. $(VENV_ACTIVATE))

# Pre-install requirements (optional).
.PHONY: requirements
requirements: $(VENV_ACTIVATE)
	@(. $(VENV_ACTIVATE) && pip install -r requirements.txt)
