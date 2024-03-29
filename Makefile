COQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _CoqProject)
COQPROJECT_Q_ARGS := $(shell grep '^-Q' _CoqProject)
ALECTRYON_CACHE := .alectryon.cache
ALECTRYON_FLAGS := $(COQPROJECT_Q_ARGS) \
	--long-line-threshold 80 \
	--cache-directory $(ALECTRYON_CACHE) --cache-compression
PROJ_VFILES := $(shell find 'src' -name "*.v")
DOC_VFILES := $(PROJ_VFILES:src/%.v=docs/%.html)

## this Makefile, as well as the test setup in Makefile.coq.local, is copied
## from std++ (https://gitlab.mpi-sws.org/iris/stdpp)

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all
.PHONY: all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	find src \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.coq .lia.cache
	rm -rf docs .alectryon.cache
.PHONY: clean

# Create Coq Makefile.
Makefile.coq: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o Makefile.coq

# Install build-dependencies
build-dep/opam: opam Makefile
	@echo "# Creating build-dep package."
	@mkdir -p build-dep
	@sed <opam -E 's/^(build|install|remove):.*/\1: []/; s/^name: *"(.*)" */name: "\1-builddep"/' >build-dep/opam
	@fgrep builddep build-dep/opam >/dev/null || (echo "sed failed to fix the package name" && exit 1) # sanity check

build-dep: build-dep/opam phony
	@# We want opam to not just instal the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing build-dep package."
	@opam install $(OPAMFLAGS) build-dep/

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
opam: ;

# alectryon targets
doc: $(DOC_VFILES)

.PHONY: doc

docs:
	@mkdir -p docs

docs/%.html: src/%.v src/%.vo | docs
	@echo "ALECTRYON $<"
	@alectryon $(ALECTRYON_FLAGS) --frontend coq+rst --backend webpage $< -o $@



# Phony wildcard targets
phony: ;
.PHONY: phony
