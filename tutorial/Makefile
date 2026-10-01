ISABELLE_VERSION ?= Isabelle2025-2
ISABELLE_HOME    ?= /Applications/$(ISABELLE_VERSION).app/bin
ISABELLE         := $(ISABELLE_HOME)/isabelle

AUTOCORRODE_DIR  := $(realpath $(CURDIR)/..)
TUTORIAL_DIR     := $(CURDIR)
PDF_NAME         ?= autocorrode_tutorial.pdf

ISABELLE_FLAGS ?= -b
USER_HOME ?= $(HOME)
AFP_COMPONENT_BASE ?=
ISABELLE_LEX_YACC_DIR ?= $(AFP_COMPONENT_BASE)/Isabelle_Lex-Yacc
ISABELLE_C_COMPONENT_BASE ?= $(AFP_COMPONENT_BASE)
ISABELLE_DOC_DIR ?= $(realpath $(ISABELLE_HOME)/../src/Doc)

# Parent session image to inherit. Built once via `make heaps`.
PARENT_IMAGE     := AutoCorrode

# All -d directories so Isabelle can resolve sessions.
DIRS             := -d "$(ISABELLE_DOC_DIR)" \
                    -d "$(AFP_COMPONENT_BASE)/Word_Lib" \
                    -d "$(ISABELLE_LEX_YACC_DIR)" \
                    -d "$(ISABELLE_C_COMPONENT_BASE)/Isabelle_C" \
                    -d .. -d .

define CHECK_ISABELLE
	@if [ ! -x "$(ISABELLE)" ]; then \
	  echo "error: '$(ISABELLE)' not found or not executable." >&2; \
	  echo "Set ISABELLE_HOME, e.g. make ISABELLE_HOME=/path/to/Isabelle/bin $@" >&2; \
	  exit 1; \
	fi
endef

.PHONY: all heaps build clean jedit

all: build

heaps:
	$(CHECK_ISABELLE)
	USER_HOME="$(USER_HOME)" $(ISABELLE) build $(DIRS) -b $(PARENT_IMAGE)

build:
	$(CHECK_ISABELLE)
	USER_HOME="$(USER_HOME)" $(ISABELLE) build $(ISABELLE_FLAGS) $(DIRS) \
		-l $(PARENT_IMAGE) AutoCorrodeTutorial
	cp output/document.pdf $(PDF_NAME)
	@echo "Wrote $(PDF_NAME)"

view: build
	open $(PDF_NAME)

clean:
	$(CHECK_ISABELLE)
	USER_HOME="$(USER_HOME)" $(ISABELLE) build $(DIRS) -c AutoCorrodeTutorial
	rm -f $(PDF_NAME)

jedit:
	$(CHECK_ISABELLE)
	USER_HOME="$(USER_HOME)" $(ISABELLE) jedit $(DIRS) -l $(PARENT_IMAGE) *.thy
