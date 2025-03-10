.PHONY: default check-archive check-tutorial check clean exercises

MAKEFILE_DIR:=$(dir $(realpath $(lastword $(MAKEFILE_LIST))))

default: tutorial
all: default

clean: tidy
	rm -rf docs/exercises docs/solutions docs/exercises.zip \
	    build TAGS _temp
#	find . -type f -regex 'cn.*' -delete
#	find . -type f -regex '*-exec.*' -delete

tidy:
	(cd src/exercises; rm -rf cn.c cn.h *-exec.* *_gen.* *_test.* tests.out cn.o constructors.h)

##############################################################################
# Exercises

EXCLUDE = cn.c cn.h run_tests.sh *-exec.c *_test.c

H = $(shell find src/exercises -type f -name *.h)
C = $(shell find src/exercises -type f -name *.c)
ALL = $(H) $(C)
BROKEN = $(shell find src/exercises -type f -name *broken*)
NOTBROKEN = $(filter-out $(BROKEN), $(C))

test:
	@echo $(NOTBROKEN)

test1:
	@echo $(filter-out foo food, baz food foo bar)



SOLUTIONS=$(patsubst src/exercises/%, docs/solutions/%, $(ALL))
EXERCISES=$(patsubst src/exercises/%, docs/exercises/%, $(ALL))
VERIFIED=$(patsubst src/exercises/%, _temp/verified/%, $(NOTBROKEN))
TESTED=$(patsubst src/exercises/%, _temp/tested/%, $(NOTBROKEN))

exercises: $(TESTED) $(VERIFIED) $(SOLUTIONS) $(EXERCISES) 

CN=cn verify
# make sure to add --output _temp again once CN testing is cleaned up
CNTEST=cn test
# CNTEST=cn test --output _temp

V=@

_temp/tested/% : src/exercises/%
	$(V)echo Testing $<
	$(V)-mkdir -p $(dir $@)
	$(V)# Next line should be reverted!
	$(V)(cd src/exercises; $(CNTEST) ../../$<   2>&1 | tee ../../$@.test.out)
	$(V)#$(CNTEST) $<   2>&1 | tee $@.test.out
	$(V)# Next line should go away!
	$(V)(cd src/exercises; rm -f cn.c cn.h run_tests.sh *-exec.c *_test.c) 2>&1 | tee $@.test.out
	$(V)-grep PASSED $@.test.out || true
	$(V)-grep FAILED $@.test.out || true
	$(V)#Reinstate this check!
	$(V)#if grep -q "fatal error" $@.test.out; then \
              exit 1; \
	    fi
	$(V)touch $@

_temp/verified/% : src/exercises/%
	$(V)@echo Verify $@
	$(V)echo Verifying $<
	$(V)@-mkdir -p $(dir $@)
	$(V)$(CN) $<   2>&1 | tee $@.verif.out

docs/exercises/%: src/exercises/%
	$(V)echo Rebuild $@
	$(V)-mkdir -p $(dir $@)
	$(V)sed -E '\|^.*--BEGIN--.*$$|,\|^.*--END--.*$$|d' $< > $@

docs/solutions/%: src/exercises/%
	$(V)echo Rebuild $@
	$(V)-mkdir -p $(dir $@)
	$(V)cat $< | sed '\|^.*--BEGIN--.*$$|d' | sed '\|^.*--END--.*$$|d' > $@

docs/exercises.zip: $(EXERCISES)
	cd docs; zip -r exercises.zip exercises > /dev/null

WORKING=$(wildcard src/exercises/list_*.c)
WORKING_AUX=$(patsubst src/exercises/%, docs/solutions/%, $(WORKING))
temp: $(WORKING_AUX) docs-exercises-dirs

# cn test --output-dir=$(HOME)/tmp read.broken.c 	

# OLD
# docs/solutions/%: src/exercises/%
# 	@-mkdir -p $(dir $@)
# 	@-mkdir -p _tests
# 	@if [ `which cn` ]; then \
# 	  if [[ "$<" = *".c"* ]]; then \
# 	    if [[ "$<" != *"broken"* && "$<" != *"partial"* && "$<" != *".DS_Store"* ]]; then \
# 	      if [[ "$<" = *".test."*c ]]; then \
# 	        echo $(CNTEST) $< && $(CNTEST) $< --output _tests; \
#               else \
# 	        echo $(CN) $< && $(CN) $<; \
# 	      fi; \
#             fi; \
# 	  fi \
# 	fi
# 	@echo Rebuild $@
# 	@cat $< | sed '\|^.*--BEGIN--.*$$|d' | sed '\|^.*--END--.*$$|d' > $@

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

tutorial: exercises docs/exercises.zip mkdocs.yml $(shell find docs -type f)
	mkdocs build --strict

serve: exercises docs/exercises.zip mkdocs.yml $(shell find docs -type f)
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
