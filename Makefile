######################################################################
#                                                                    #
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. #
# SPDX-License-Identifier: MIT                                       #
#                                                                    #
# Makefile for Isabelle/HOL AutoCorrode sessions                     #
#                                                                    #
######################################################################

.DEFAULT_GOAL: jedit
.PHONY: check-afp-components register-afp-components \
        build-isabelle-c build-micro-c-isabelle-c-adapter \
        build-shallow-state build-shallow-state-logic \
        build-shallow-micro-rust build-shallow-micro-c \
        build-micro-c-parsing-frontend \
        build-micro-c-parser-tests build-micro-c-examples \
        language-isolation-tests \
        c-baseline c-prototype build parser-tests jedit tutorial \
        build-ic2 ic2 ic2-status ic2-stop

# Set this to the directory containing the Isabelle2025-2 binary.
ISABELLE_HOME?=/Applications/Isabelle2025-2.app/bin
# Set this to your home directory.
USER_HOME?=$(HOME)
# Set this to the installed AFP snapshot's thys directory.
AFP_COMPONENT_BASE?=
ISABELLE_LEX_YACC_DIR?=$(AFP_COMPONENT_BASE)/Isabelle_Lex-Yacc
ISABELLE_C_COMPONENT_BASE?=$(AFP_COMPONENT_BASE)
# Isabelle/C depends on the Isar_Ref documentation session.
ISABELLE_DOC_DIR?=$(abspath $(ISABELLE_HOME)/../src/Doc)

# Set this option to accept `sorry`'ed proofs.
ifdef QUICK_AND_DIRTY
	ISABELLE_FLAGS += -o quick_and_dirty
endif

HOST=$(shell uname -s)
ifeq ($(HOST),Darwin)
	AVAILABLE_CORES?=$(shell sysctl -n hw.physicalcpu)
else ifeq ($(HOST),Linux)
	AVAILABLE_CORES?=$(shell nproc)
else
	$(error Unsupported host platform)
endif

# -j 1 determines the number of parallel jobs; threads=n sets the number
# of cores for the single session build.
ISABELLE_FLAGS?=-b -j 1 -o "threads=$(AVAILABLE_CORES)" -v
ISABELLE_JEDIT_FLAGS?=

ISABELLE_FLAGS += $(ISABELLE_REMOTE)
ISABELLE_JEDIT_FLAGS += $(ISABELLE_REMOTE)

MICRO_C_NEUTRAL_SESSION_DIRS = \
	-d "$(AFP_COMPONENT_BASE)/Word_Lib" \
	-d Data_Structures \
	-d Misc \
	-d Lenses_And_Other_Optics \
	-d Shallow_Computation

AUTOCORRODE_SESSION_DIRS = \
	-d "$(ISABELLE_DOC_DIR)" \
	-d "$(AFP_COMPONENT_BASE)/Word_Lib" \
	-d "$(ISABELLE_LEX_YACC_DIR)" \
	-d "$(ISABELLE_C_COMPONENT_BASE)/Isabelle_C" \
	-d .

check-afp-components:
	@test -n "$(AFP_COMPONENT_BASE)" || { \
		echo "AFP_COMPONENT_BASE must name the installed AFP thys directory" >&2; \
		exit 1; \
	}
	@for component in Word_Lib Isabelle_Lex-Yacc Isabelle_C; do \
		test -d "$(AFP_COMPONENT_BASE)/$$component" || { \
			echo "missing AFP component: $(AFP_COMPONENT_BASE)/$$component" >&2; \
			exit 1; \
		}; \
	done

jedit: check-afp-components
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle jedit $(ISABELLE_JEDIT_FLAGS) \
		$(AUTOCORRODE_SESSION_DIRS) -R AutoCorrode &

register-afp-components: check-afp-components
	$(ISABELLE_HOME)/isabelle components -u $(AFP_COMPONENT_BASE)/Word_Lib
	$(ISABELLE_HOME)/isabelle components -u $(ISABELLE_LEX_YACC_DIR)

build-isabelle-c: check-afp-components
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		-d "$(ISABELLE_DOC_DIR)" \
		-d "$(ISABELLE_C_COMPONENT_BASE)/Isabelle_C" \
		Isabelle_C

build-micro-c-isabelle-c-adapter: build-isabelle-c
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		-d "$(ISABELLE_DOC_DIR)" \
		-d "$(ISABELLE_C_COMPONENT_BASE)/Isabelle_C" \
		-d Micro_C_Isabelle_C_Adapter \
		Micro_C_Isabelle_C_Adapter

build-shallow-state: check-afp-components
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Shallow_State

build-shallow-state-logic: build-shallow-state
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Shallow_State_Logic

build-shallow-micro-rust: build-shallow-state
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Shallow_Micro_Rust

build-shallow-micro-c: check-afp-components
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Shallow_Micro_C

build-micro-c-parsing-frontend: build-micro-c-isabelle-c-adapter
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Micro_C_Parsing_Frontend

build-micro-c-parser-tests: build-micro-c-parsing-frontend
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Micro_C_Parser_Tests

build-micro-c-examples: build-micro-c-parsing-frontend
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Micro_C_Examples

language-isolation-tests: check-afp-components
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Language_Isolation_Tests

c-baseline: build-micro-c-isabelle-c-adapter language-isolation-tests build

c-prototype: build-shallow-state build-shallow-state-logic build-shallow-micro-rust \
	build-shallow-micro-c build-micro-c-parsing-frontend build-micro-c-parser-tests \
	build-micro-c-examples parser-tests language-isolation-tests build

build: check-afp-components
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) \
		$(AUTOCORRODE_SESSION_DIRS) AutoCorrode

parser-tests: check-afp-components
	USER_HOME="$(USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Micro_Rust_Parser_Tests

# Build the slide-deck tutorial in tutorial/. Inherits the AutoCorrode
# parent heap, so run `make build` first if it is not built yet.
tutorial: check-afp-components
	$(MAKE) -C tutorial \
		ISABELLE_HOME="$(ISABELLE_HOME)" \
		USER_HOME="$(USER_HOME)" \
		AFP_COMPONENT_BASE="$(abspath $(AFP_COMPONENT_BASE))" \
		ISABELLE_LEX_YACC_DIR="$(abspath $(ISABELLE_LEX_YACC_DIR))" \
		ISABELLE_C_COMPONENT_BASE="$(abspath $(ISABELLE_C_COMPONENT_BASE))" \
		ISABELLE_DOC_DIR="$(ISABELLE_DOC_DIR)" \
		build

#######################################
# ic2 headless session server (I/R)
#######################################

IC2_NAME ?= AutoCorrode
IC2_FLAGS ?= --daemon
IC2_FLAGS += $(ISABELLE_REMOTE)

build-ic2:
	$(MAKE) -C ic2 ISABELLE_HOME=$(ISABELLE_HOME) build

ic2: register-afp-components build-ic2
	$(ISABELLE_HOME)/isabelle ic2 server start $(IC2_FLAGS) -n $(IC2_NAME) -d . -l HOL
	@echo ''
	@echo '  ic2 server "$(IC2_NAME)" launched. Follow its console with:'
	@echo '      $(ISABELLE_HOME)/isabelle ic2 server attach -n $(IC2_NAME)'
	@echo '  Status: make ic2-status   |   Stop: make ic2-stop'
	@echo ''

ic2-status: build-ic2
	$(ISABELLE_HOME)/isabelle ic2 server status

ic2-stop: build-ic2
	$(ISABELLE_HOME)/isabelle ic2 server stop -n $(IC2_NAME)
