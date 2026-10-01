######################################################################
#                                                                    #
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. #
# SPDX-License-Identifier: MIT                                       #
#                                                                    #
# Makefile for Isabelle/HOL AutoCorrode sessions                     #
#                                                                    #
######################################################################

.DEFAULT_GOAL: jedit
.PHONY: register-afp-components prepare-isabelle-c test-isabelle-c-preparation \
        check-isabelle-c-boundary build-isabelle-c \
        build-micro-c-isabelle-c-adapter build-shallow-micro-c \
        build-micro-c-parsing-frontend build-micro-c-parser-tests \
        language-isolation-tests c-baseline c-prototype build parser-tests \
        jedit tutorial build-ic2 ic2 ic2-status ic2-stop

# Set this to the directory containing the Isabelle2025-2 binary
ISABELLE_HOME?=/Applications/Isabelle2025-2.app/bin
# Set this to your home directory
USER_HOME?=$(HOME)
# Set this to where you maintain, or want to maintain, AFP dependencies
AFP_COMPONENT_BASE?=./dependencies/afp
# Source checkout for the pinned AFP Isabelle/C entry. The preparation step
# copies and patches this component under the worktree instead of changing the
# source checkout.
AFP_SOURCE_BASE?=$(AFP_COMPONENT_BASE)
# Pinned Isabelle_Lex-Yacc provider used by the isolated top-level build.
ISABELLE_LEX_YACC_DIR?=$(AFP_SOURCE_BASE)/Isabelle_Lex-Yacc
# Worktree-private destination for the patched Isabelle/C component.
ISABELLE_C_COMPONENT_BASE?=./dependencies/afp
# Isolate C baseline heaps and component registrations from machine-global AFP
# installations, which may provide another session named Isabelle_C. Isabelle
# derives ISABELLE_HOME_USER from USER_HOME during startup.
ISABELLE_C_USER_HOME?=$(abspath ./dependencies/isabelle-c-user-home)
# Isabelle/C depends on the Isar_Ref documentation session.
ISABELLE_DOC_DIR?=$(abspath $(ISABELLE_HOME)/../src/Doc)
# Set this option to accept `sorry`'ed proofs
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

# -j 1 determines amount of parallel jobs,
# threads=n sets amount of cores per job. We are building a single
# session, so we want 1 job with as much cores as are available
ISABELLE_FLAGS?=-b -j 1 -o "threads=$(AVAILABLE_CORES)" -v
ISABELLE_JEDIT_FLAGS?=

ISABELLE_FLAGS += $(ISABELLE_REMOTE)
ISABELLE_JEDIT_FLAGS += $(ISABELLE_REMOTE)

# Explicit neutral dependency closure for the isolated C builds. Avoiding
# `-d .` keeps unrelated parser sessions and their AFP components out of the
# C frontend process.
MICRO_C_NEUTRAL_SESSION_DIRS = \
	-d "$(AFP_COMPONENT_BASE)/Word_Lib" \
	-d Data_Structures \
	-d Misc \
	-d Lenses_And_Other_Optics \
	-d Shallow_Computation

# Complete dependency closure for commands that load the top-level ROOTS
# catalog. External AFP sessions stay out of ROOTS to avoid duplicate session
# names when another AFP snapshot is registered globally.
AUTOCORRODE_SESSION_DIRS = \
	-d "$(ISABELLE_DOC_DIR)" \
	-d "$(AFP_COMPONENT_BASE)/Word_Lib" \
	-d "$(ISABELLE_LEX_YACC_DIR)" \
	-d "$(ISABELLE_C_COMPONENT_BASE)/Isabelle_C" \
	-d .

jedit: prepare-isabelle-c
	USER_HOME="$(ISABELLE_C_USER_HOME)" \
		$(ISABELLE_HOME)/isabelle jedit $(ISABELLE_JEDIT_FLAGS) \
		$(AUTOCORRODE_SESSION_DIRS) -R AutoCorrode &

register-afp-components:
	$(ISABELLE_HOME)/isabelle components -u $(AFP_COMPONENT_BASE)/Word_Lib

prepare-isabelle-c:
	AFP_SOURCE_BASE="$(AFP_SOURCE_BASE)" \
		ISABELLE_C_COMPONENT_BASE="$(ISABELLE_C_COMPONENT_BASE)" \
		./tools/isabelle-c/prepare-isabelle-c.sh

test-isabelle-c-preparation:
	AFP_SOURCE_BASE="$(AFP_SOURCE_BASE)" \
		./tools/isabelle-c/test-prepare-isabelle-c.sh

check-isabelle-c-boundary:
	./tools/isabelle-c/check-isabelle-c-boundary.sh

build-isabelle-c: prepare-isabelle-c
	USER_HOME="$(ISABELLE_C_USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		-d "$(ISABELLE_DOC_DIR)" \
		-d "$(ISABELLE_C_COMPONENT_BASE)/Isabelle_C" \
		Isabelle_C

build-micro-c-isabelle-c-adapter: build-isabelle-c
	USER_HOME="$(ISABELLE_C_USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		-d "$(ISABELLE_DOC_DIR)" \
		-d "$(ISABELLE_C_COMPONENT_BASE)/Isabelle_C" \
		-d Micro_C_Isabelle_C_Adapter \
		Micro_C_Isabelle_C_Adapter

build-shallow-micro-c:
	USER_HOME="$(ISABELLE_C_USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(MICRO_C_NEUTRAL_SESSION_DIRS) \
		-d Shallow_Micro_C \
		Shallow_Micro_C

build-micro-c-parsing-frontend: build-micro-c-isabelle-c-adapter
	USER_HOME="$(ISABELLE_C_USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		-d "$(ISABELLE_DOC_DIR)" \
		-d "$(ISABELLE_C_COMPONENT_BASE)/Isabelle_C" \
		$(MICRO_C_NEUTRAL_SESSION_DIRS) \
		-d Shallow_Micro_C \
		-d Micro_C_Isabelle_C_Adapter \
		-d Micro_C_Parsing_Frontend \
		Micro_C_Parsing_Frontend

build-micro-c-parser-tests: build-micro-c-parsing-frontend
	USER_HOME="$(ISABELLE_C_USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		-d "$(ISABELLE_DOC_DIR)" \
		-d "$(ISABELLE_C_COMPONENT_BASE)/Isabelle_C" \
		$(MICRO_C_NEUTRAL_SESSION_DIRS) \
		-d Shallow_Micro_C \
		-d Micro_C_Isabelle_C_Adapter \
		-d Micro_C_Parsing_Frontend \
		-d Micro_C_Parser_Tests \
		Micro_C_Parser_Tests

language-isolation-tests: prepare-isabelle-c
	USER_HOME="$(ISABELLE_C_USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Language_Isolation_Tests

c-baseline: test-isabelle-c-preparation check-isabelle-c-boundary \
            build-micro-c-isabelle-c-adapter language-isolation-tests build

c-prototype: test-isabelle-c-preparation check-isabelle-c-boundary \
             build-micro-c-parser-tests language-isolation-tests build

build: prepare-isabelle-c
	USER_HOME="$(ISABELLE_C_USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) \
		$(AUTOCORRODE_SESSION_DIRS) AutoCorrode

parser-tests: prepare-isabelle-c
	USER_HOME="$(ISABELLE_C_USER_HOME)" \
		$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -o document=false \
		$(AUTOCORRODE_SESSION_DIRS) \
		Micro_Rust_Parser_Tests

# Build the slide-deck tutorial in tutorial/. Inherits the AutoCorrode
# parent heap, so run `make build` first if it isn't built yet.
tutorial: prepare-isabelle-c
	$(MAKE) -C tutorial \
		ISABELLE_HOME="$(ISABELLE_HOME)" \
		USER_HOME="$(ISABELLE_C_USER_HOME)" \
		AFP_COMPONENT_BASE="$(abspath $(AFP_COMPONENT_BASE))" \
		ISABELLE_LEX_YACC_DIR="$(abspath $(ISABELLE_LEX_YACC_DIR))" \
		ISABELLE_C_COMPONENT_BASE="$(abspath $(ISABELLE_C_COMPONENT_BASE))" \
		ISABELLE_DOC_DIR="$(ISABELLE_DOC_DIR)" \
		build

#######################################
# ic2 headless session server (I/R)
#######################################
# `make ic2` starts a warm, headless PIDE daemon (ic2) for the full AutoCorrode
# session: the HOL heap is loaded and AutoCorrode's theories are
# checked/developed against it via `isabelle ic2 check ...` or the I/R REPL.
# `make ic2-status` surveys running servers and `make ic2-stop` shuts this one
# down. See ic2/README.md for the CLI.
#
# ic2 is plain Isabelle/Scala (no proof session to build): the component must be
# registered and lib/ic2.jar compiled once via ic2/Makefile before these targets
# work. build-ic2 delegates there (idempotent).

# Server name, so `make ic2-stop` / `-status` and `isabelle ic2` agree on the slot.
IC2_NAME ?= AutoCorrode

# Flags for `isabelle ic2 server start`. --daemon detaches and returns once the
# warm session is ready. Override IC2_FLAGS to run in the foreground, or to add
# --mcp / --no-iq / -N (no build) / -o ... etc.
IC2_FLAGS ?= --daemon
# Proxy `server start` to the same remote host as build/jedit, if configured.
IC2_FLAGS += $(ISABELLE_REMOTE)

# Register the ic2 component and (re)build lib/ic2.jar. Idempotent.
build-ic2:
	$(MAKE) -C ic2 ISABELLE_HOME=$(ISABELLE_HOME) build

# Start a daemonised ic2 server for the full AutoCorrode session, on the HOL
# heap. Run `make build` first to have the AutoCorrode heap ready; otherwise the
# cold build runs in the background (see ic2/README.md).
ic2: register-afp-components build-ic2
	$(ISABELLE_HOME)/isabelle ic2 server start $(IC2_FLAGS) -n $(IC2_NAME) -d . -l HOL
	@echo ''
	@echo '  ic2 server "$(IC2_NAME)" launched. Follow its console (build progress + logs) with:'
	@echo '      $(ISABELLE_HOME)/isabelle ic2 server attach -n $(IC2_NAME)'
	@echo '  Status: make ic2-status   |   Stop: make ic2-stop'
	@echo ''

# Survey every running ic2 server.
ic2-status: build-ic2
	$(ISABELLE_HOME)/isabelle ic2 server status

# Stop the server (override IC2_NAME to target a differently-named one).
ic2-stop: build-ic2
	$(ISABELLE_HOME)/isabelle ic2 server stop -n $(IC2_NAME)
