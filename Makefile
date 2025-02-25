.PHONY: default check-archive check-tutorial check clean exercises

MAKEFILE_DIR:=$(dir $(realpath $(lastword $(MAKEFILE_LIST))))

default: tutorial
all: default

clean:
	rm -rf docs/exercises docs/solutions docs/exercises.zip \
	    build TAGS _tests

##############################################################################
# Exercises

SRC_EXERCISES=$(shell find src/exercises -type f)
SOLUTIONS=$(patsubst src/exercises/%, docs/solutions/%, $(SRC_EXERCISES))
EXERCISES=$(patsubst src/exercises/%, docs/exercises/%, $(SRC_EXERCISES))

CN=cn verify
CNTEST=cn test

exercises: docs-exercises-dirs $(EXERCISES) $(SOLUTIONS)

docs-exercises-dirs:
	mkdir -p docs/exercises
	mkdir -p docs/solutions

docs/exercises/%: src/exercises/%
	@echo Rebuild $@
	@-mkdir -p $(dir $@)
	@sed -E '\|^.*--BEGIN--.*$$|,\|^.*--END--.*$$|d' $< > $@

docs/solutions/%: src/exercises/%
	@-mkdir -p $(dir $@)
	@-mkdir -p _tests
	@if [ `which cn` ]; then \
	  if [[ "$<" = *".c"* ]]; then \
	    if [[ "$<" != *"broken"* ]]; then \
	      if [[ "$<" = *".test."*c ]]; then \
	        echo $(CNTEST) $< && $(CNTEST) test $< --output _tests; \
              else \
	        echo $(CN) $< && $(CN) $<; \
	      fi; \
            fi; \
	  fi \
	fi
	@echo Rebuild $@
	@cat $< | sed '\|^.*--BEGIN--.*$$|d' | sed '\|^.*--END--.*$$|d' > $@

docs/exercises.zip: $(EXERCISES)
	cd docs; zip -r exercises.zip exercises > /dev/null

WORKING=$(wildcard src/exercises/list_*.c)
WORKING_AUX=$(patsubst src/exercises/%, docs/solutions/%, $(WORKING))
temp: $(WORKING_AUX) docs-exercises-dirs

##############################################################################
# Check that the examples all run correctly

CN_PATH?=cn verify

check-archive:
	@echo Check archive examples
	@$(MAKEFILE_DIR)/src/example-archive/check-all.sh "$(CN_PATH)"

check-tutorial:
	@echo Check tutorial exercises
	@$(MAKEFILE_DIR)/check.sh "$(CN_PATH)"

check: check-tutorial check-archive

##############################################################################
# Tutorial document

tutorial: exercises mkdocs.yml $(shell find docs -type f)
	mkdocs build --strict

serve: exercises mkdocs.yml $(shell find docs -type f)
	mkdocs serve

##############################################################################
# Misc

TAGS:
	@echo Rebuilding TAGS
	@etags src/tutorial.adoc $(SRC_EXERCISES)

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
