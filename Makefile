.PHONY: default check-archive check-tutorial check clean exercises

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

SRC_EXAMPLES=$(shell find src/examples -type f)
SOLUTIONS=$(patsubst src/examples/%, build/solutions/%, $(SRC_EXAMPLES))
EXERCISES=$(patsubst src/examples/%, build/exercises/%, $(SRC_EXAMPLES))

CN=cn verify

exercises: $(EXERCISES) $(SOLUTIONS)

build/exercises/%: src/examples/%
	@echo Rebuild $@
	@-mkdir -p $(dir $@)
	@sed -E '\|^.*--BEGIN--.*$$|,\|^.*--END--.*$$|d' $< > $@

build/solutions/%: src/examples/%
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

build/exercises.zip: $(EXERCISES)
	cd build; zip -r exercises.zip exercises > /dev/null


##############################################################################
# Check that the examples all run correctly 

CN_PATH?="cn verify"

check-archive: 
	@echo Check archive examples
	@$(MAKEFILE_DIR)/src/example-archive/check-all.sh $(CN_PATH)

check-tutorial:
	@echo Check tutorial examples
	@$(MAKEFILE_DIR)/check.sh $(CN_PATH)

check: check-tutorial check-archive 

##############################################################################
# Tutorial document

build/tutorial.adoc build/style.css build/asciidoctor.css: src/tutorial.adoc
	@echo Create build/tutorial.adoc
	@sed -E 's/include_example\((.+)\)/.link:\1[\1]\n[source,c]\n----\ninclude::\1\[\]\n----/g' $< > $@
	@cp src/style.css build
	@cp src/asciidoctor.css build

build/images: src/images
	cp -r $< $@

build/tutorial.html: build/tutorial.adoc $(SRC_EXAMPLES) build/images
	asciidoctor --doctype book $< -o $@
	@rm build/tutorial.adoc

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
