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

SOLUTIONS=$(patsubst src/exercises/%, docs/solutions/%, $(ALL))
EXERCISES=$(patsubst src/exercises/%, docs/exercises/%, $(ALL))
VERIFIED=$(patsubst src/exercises/%, _temp/verified/%, $(NOTBROKEN))

#TESTED=$(patsubst src/exercises/%, _temp/tested/%, $(NOTBROKEN))
# TEMPORARY:
TESTED = \
  _temp/tested/abs_mem_struct.c \
  _temp/tested/bcp_framerule.c \
  _temp/tested/slf_quadruple_mem.c \
  _temp/tested/_temp/funcs2-exec.c \
  _temp/tested/_temp/const_example-exec.c \
  _temp/tested/const_example_lessgood.c \
  _temp/tested/transpose2.c \
  _temp/tested/slf2_basic_quadruple.signed.c \
  _temp/tested/add_read.c \
  _temp/tested/slf8_basic_transfer.c \
  _temp/tested/slf3_basic_inplace_double.c \
  _temp/tested/add_1.c \
  _temp/tested/array_load.c \
  _temp/tested/slf0_basic_incr.c \
  _temp/tested/runway/funcs2.c \
  _temp/tested/zero.c \
  _temp/tested/slf_incr2_noalias.c \
  _temp/tested/slf10_basic_ref.c \
  _temp/tested/add_2.c \
  _temp/tested/add_two_array.c \
  _temp/tested/transpose.c \
  _temp/tested/read2.c \
  _temp/tested/read.c \
  _temp/tested/slf1_basic_example_let.c \
  _temp/tested/slf_incr2_alias.c \
  _temp/tested/abs_mem.c \
  _temp/tested/swap_array.c \
  _temp/tested/const_example.c \
  _temp/tested/add.partial.c \
  _temp/tested/init_point.c \
  _temp/tested/min3/min3.fixed.c \
  _temp/tested/min3/min3.test.partial.c \
  _temp/tested/min3/min3.partial.c \
  _temp/tested/slf_incr2.c \
  _temp/tested/id_by_div.fixed.c \
  _temp/tested/slf2_basic_quadruple.c \
  _temp/tested/slf18_two_dice.c \
  _temp/tested/swap.c \
  _temp/tested/slf1_basic_example_let.signed.c \
  _temp/tested/slf9_basic_transfer_aliased.c \
  _temp/tested/array_load2.c \
  _temp/tested/add_0.c \
  _temp/tested/abs.c \
  _temp/tested/slf0_basic_incr.signed.c \
  _temp/tested/slf15_basic_succ_using_incr_attempt_.c 

exercises: $(TESTED) $(VERIFIED) $(SOLUTIONS) $(EXERCISES) 

CN=cn verify
CNTEST=cn test --output ../../_temp
# CNTEST=cn test --output _temp

# Control verbosity (run make with V= to show everything that's happening)
V=@

_temp/tested/% : src/exercises/%
	$(V)echo Testing $<
	$(V)-mkdir -p $(dir $@)
	$(V)(cd src/exercises; $(CNTEST) ../../$<   2>&1 | tee ../../$@.test.out)
	$(V)-grep PASSED $@.test.out || true
	$(V)-grep FAILED $@.test.out || true
	@# This should not be needed!
	$(V)if grep -q "fatal error\\|Failed to compile" $@.test.out; then \
              exit 1; \
	      else \
	      echo NO FAIL $@; \
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
