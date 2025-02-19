.PHONY: default check-archive check-tutorial check clean exercises

MAKEFILE_DIR:=$(dir $(realpath $(lastword $(MAKEFILE_LIST))))

default: tutorial
all: default

clean:
	rm -rf docs/exercises docs/solutions docs/exercises.zip build TAGS

##############################################################################
# Exercises

SRC_EXAMPLES=$(shell find src/examples -type f)
SOLUTIONS=$(patsubst src/examples/%, docs/solutions/%, $(SRC_EXAMPLES))
EXERCISES=$(patsubst src/examples/%, docs/exercises/%, $(SRC_EXAMPLES))

CN=cn verify

exercises: docs-exercises-dirs $(EXERCISES) $(SOLUTIONS)

docs-exercises-dirs:
	mkdir -p docs/exercises
	mkdir -p docs/solutions

docs/exercises/%: src/examples/%
	@echo Rebuild $@
	@-mkdir -p $(dir $@)
	@sed -E '\|^.*--BEGIN--.*$$|,\|^.*--END--.*$$|d' $< > $@

docs/solutions/%: src/examples/%
	@-mkdir -p $(dir $@)
	@if [ `which cn` ]; then \
	  if [[ "$<" = *".c"* ]]; then \
	    if [[ "$<" != *"broken"* ]]; then \
	       echo $(CN) $< && $(CN) $<; \
	    fi; \
	  fi \
	fi
	@echo Rebuild $@
	@cat $< | sed '\|^.*--BEGIN--.*$$|d' | sed '\|^.*--END--.*$$|d' > $@

docs/exercises.zip: $(EXERCISES)
	cd docs; zip -r exercises.zip exercises > /dev/null

WORKING=$(wildcard src/examples/list_*.c)
WORKING_AUX=$(patsubst src/examples/%, docs/solutions/%, $(WORKING))
temp: $(WORKING_AUX) docs-exercises-dirs

##############################################################################
# Check that the examples all run correctly

CN_PATH?=cn verify

check-archive: 
	@echo Check archive examples
	@$(MAKEFILE_DIR)/src/example-archive/check-all.sh "$(CN_PATH)"

check-tutorial:
	@echo Check tutorial examples
	@$(MAKEFILE_DIR)/check.sh "$(CN_PATH)"

check: check-tutorial check-archive

##############################################################################
# Tutorial document

tutorial: exercises docs/exercises.zip mkdocs.yml $(shell find docs -type f)
	mkdocs build --strict

serve: exercises docs/exercises.zip mkdocs.yml $(shell find docs -type f)
	mkdocs serve

##############################################################################
# Misc

TAGS:
	@echo Rebuilding TAGS
	@etags src/tutorial.adoc $(SRC_EXAMPLES)

##############################################################################
# Personal and site-specific stuff

bcp: TAGS
	$(MAKE) default
	osascript \
	   -e 'tell application "Safari"' \
	     -e 'tell its first document' \
	       -e 'set its URL to (get its URL)' \
	     -e 'end tell' \
	   -e 'activate' \
	   -e 'end tell'
