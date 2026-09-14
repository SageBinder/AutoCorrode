# Makefile for the Micro_Rust_Parser_Timing Isabelle/Scala component.

ISABELLE_VERSION ?= Isabelle2025-2
ISABELLE_HOME ?= /Applications/$(ISABELLE_VERSION).app/bin
ISABELLE ?= $(ISABELLE_HOME)/isabelle

COMPONENT_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
REPOSITORY_DIR := $(realpath $(COMPONENT_DIR)/..)
AFP_COMPONENT_BASE ?= $(REPOSITORY_DIR)/dependencies/afp
AFP_WORD_LIB := $(AFP_COMPONENT_BASE)/Word_Lib
FIXTURE_SESSION := Micro_Rust_Parser_Timing_Fixture

.PHONY: all register register-afp build jar fixture test test-unit test-e2e clean help

all: build

register:
	$(ISABELLE) components -u $(COMPONENT_DIR)

register-afp:
	$(ISABELLE) components -u $(AFP_WORD_LIB)

build: register
	$(ISABELLE) scala_build

jar: register
	$(ISABELLE) scala_build -f

fixture: register-afp build
	$(ISABELLE) build -b -j 2 -o threads=2 \
		-d $(REPOSITORY_DIR) -d $(COMPONENT_DIR) $(FIXTURE_SESSION)

test: test-unit test-e2e

test-unit: build
	$(ISABELLE) urust_timing_test unit

test-e2e: fixture
	$(ISABELLE) urust_timing_test e2e $(FIXTURE_SESSION)

clean:
	$(RM) $(COMPONENT_DIR)/lib/micro_rust_parser_timing.jar

help:
	@echo "Targets:"
	@echo "  build      register and compile the component"
	@echo "  jar        force a fresh component rebuild"
	@echo "  fixture    build the neutral two-theory fixture with parallel workers"
	@echo "  test       run unit and built-session tests"
	@echo "  test-unit  run pure record/aggregation/JSON tests"
	@echo "  test-e2e   build and inspect the fixture session"
	@echo "  clean      remove the generated jar"
	@echo ""
	@echo "Variables:"
	@echo "  AFP_COMPONENT_BASE  directory containing Word_Lib"
