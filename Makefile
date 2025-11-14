# -------- Makefile (multi-file Coq + docs) --------

# Tools
COQC      ?= rocq c
COQDOC    ?= rocq doc
COQDEP    ?= coqdep

# Flags
COQFLAGS  ?= -q
COQDOCFLAGS ?= --html --utf8 --toc --no-index

# Sources (all .v in this directory; or set explicitly: VFILES = a.v b.v ...)
VFILES    := $(wildcard *.v)
VOFILES   := $(VFILES:.v=.vo)

# Docs output directory
DOCSDIR   ?= docs

# Dependency file
DEPFILE   := .coqdeps

# Default target
.PHONY: all
all: $(VOFILES) doc

# Compile each .v -> .vo
%.vo: %.v
	$(COQC) $(COQFLAGS) $<

# Generate (or refresh) dependencies
# Run this first so that included .v deps are known before building .vo
$(DEPFILE): $(VFILES)
	@echo "Generating Coq dependencies..."
	@$(COQDEP) $(COQFLAGS) $(VFILES) > $(DEPFILE)

# Include dependencies if present
# (This makes 'make' rebuild files in the right order.)
-include $(DEPFILE)

# Documentation for all files, into docs/
.PHONY: doc
doc: $(VFILES)
	@mkdir -p $(DOCSDIR)
	$(COQDOC) $(COQDOCFLAGS) -d $(DOCSDIR) $(VFILES)

# Clean
.PHONY: clean
clean:
	rm -f $(VOFILES) *.vok *.vos *.glob .*.aux
	rm -f $(DEPFILE)
	rm -rf $(DOCSDIR)

# Convenience: just build deps
.PHONY: deps
deps: $(DEPFILE)

# ---------------------------------------------------
