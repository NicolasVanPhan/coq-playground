# File: Makefile

COQC=coqc
COQDOC=coqdoc
COQFLAGS=-q

# Your source file
SRC=peano.v

# Base name (without extension)
BASE=$(basename $(SRC))

# Targets
all: $(BASE).vo doc

# Compile the .v file
$(BASE).vo: $(SRC)
	$(COQC) $(COQFLAGS) $(SRC)

# Generate documentation with coqdoc
doc: $(SRC)
	$(COQDOC) --html --parse-comments $(SRC)

# Clean up build artifacts
clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux *.html *.css

.PHONY: all clean doc

# end
