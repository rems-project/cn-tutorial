.PHONY: default check clean exercises

MAKEFILE_DIR:=$(dir $(realpath $(lastword $(MAKEFILE_LIST))))

default: build exercises build/tutorial.html build/exercises.zip

clean:
	rm -rf build TAGS

build:
	mkdir -p build
	mkdir -p build/exercises
	mkdir -p build/solutions

##############################################################################
# Exercises

SRC_EXAMPLES=$(wildcard src/examples/*)
SOLUTIONS=$(patsubst src/examples/%, build/solutions/%, $(SRC_EXAMPLES))
EXERCISES=$(patsubst src/examples/%, build/exercises/%, $(SRC_EXAMPLES))

exercises: $(EXERCISES) $(SOLUTIONS)

build/exercises/%: src/examples/%
#	sed -E '/^--BEGIN--$$/,/^--END--$$/d' $< > $@
	@echo Rebuild $@
	@sed -E '\|^.*--BEGIN--.*$$|,\|^.*--END--.*$$|d' $< > $@

build/solutions/%: src/examples/%
	@if [[ "$<" = *".c"* ]]; then \
	  if [[ "$<" != *"broken"* ]]; then \
	     echo cn $< && cn $<; \
	  fi; \
	fi
#	cat $< | sed '/^--BEGIN--$$/d' | sed '/^--END--$$/d' > $@
	@echo Rebuild $@
	@cat $< | sed '\|^.*--BEGIN--.*$$|d' | sed '\|^.*--END--.*$$|d' > $@

build/exercises.zip: $(EXERCISES)
	cd build; zip -r exercises.zip exercises

check:
	@echo Check examples
	@$(MAKEFILE_DIR)/check.sh

##############################################################################
# Tutorial document

build/tutorial.adoc: src/tutorial.adoc
	cp $< $@

build/images: src/images
	cp -r $< $@

build/tutorial.html: build/tutorial.adoc $(SRC_EXAMPLES) build/images
	asciidoctor --doctype book $< -o $@

##############################################################################
# Misc

TAGS:
	etags src/tutorial.adoc $(SRC_EXAMPLES)

##############################################################################
# Site-specific stuff

upenn-install: default
	rm -rf $(HOME)/pub/courses/6700-SL-2024/current/CN
	mkdir $(HOME)/pub/courses/6700-SL-2024/current/CN
	cp -r build/* $(HOME)/pub/courses/6700-SL-2024/current/CN
