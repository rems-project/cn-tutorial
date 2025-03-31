.PHONY: default check-archive check-tutorial check clean tidy \
	exercises rebuild tutorial

MAKEFILE_DIR:=$(dir $(realpath $(lastword $(MAKEFILE_LIST))))

default: tutorial
all: default

clean: tidy
	rm -rf docs/exercises docs/solutions docs/exercises.zip \
	    build TAGS _temp _tests
	find . -type f -regex '*.tmp' -delete

tidy:
	(cd src/exercises; rm -rf cn.c cn.h *-exec.* *_gen.* *_test.* tests.out cn.o constructors.h)

##############################################################################
# Exercises

H = $(shell find src/exercises -type f -name *.h)
C = $(shell find src/exercises -type f -name *.c)
ALL = $(H) $(C)

TESTONLY = $(shell find src/exercises -type f -name *.test*.c)
VERIFONLY = $(shell find src/exercises -type f -name *.verif*.c)

BROKEN = $(shell find src/exercises -type f -name *broken* -or -name *partial*)
VERIF = $(filter-out $(BROKEN) $(TESTONLY), $(C))
TEST = $(filter-out $(BROKEN) $(VERIFONLY), $(C))

SOLUTIONS=$(patsubst src/exercises/%, docs/solutions/%, $(ALL))
EXERCISES=$(patsubst src/exercises/%, docs/exercises/%, $(ALL))
VERIFIED=$(patsubst src/exercises/%, _temp/verified/%, $(VERIF))

#TESTED=$(patsubst src/exercises/%, _temp/tested/%, $(TEST))
# TEMPORARY:
TESTED = $(patsubst src/exercises/%, _temp/tested/%, $(TESTONLY)) \
  _temp/tested/abs_mem_struct.c \
  _temp/tested/bcp_framerule.c \
  _temp/tested/slf_quadruple_mem.c \
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
  _temp/tested/between.c \
  _temp/tested/array_read_two.c \
  _temp/tested/transpose.c \
  _temp/tested/read2.c \
  _temp/tested/read.c \
  _temp/tested/slf1_basic_example_let.c \
  _temp/tested/slf_incr2_alias.c \
  _temp/tested/abs_mem.c \
  _temp/tested/array_swap.c \
  _temp/tested/const_example.c \
  _temp/tested/add.partial.c \
  _temp/tested/init_point.c \
  _temp/tested/min3/min3.fixed.c \
  _temp/tested/min3/min3.partial.c \
  _temp/tested/min3/min3.partial1.c \
  _temp/tested/slf_incr2.c \
  _temp/tested/id_by_div/id_by_div.fixed.c \
  _temp/tested/slf2_basic_quadruple.c \
  _temp/tested/swap.c \
  _temp/tested/slf1_basic_example_let.signed.c \
  _temp/tested/slf9_basic_transfer_aliased.c \
  _temp/tested/array_load2.c \
  _temp/tested/add_0.c \
  _temp/tested/abs.c \
  _temp/tested/slf0_basic_incr.signed.c \
  _temp/tested/slf15_basic_succ_using_incr_attempt_.c

# Extra dependencies
_temp/tested/list/*.c : src/exercises/list/*.h
_temp/verified/list/*.c : src/exercises/list/*.h

# NOT WORKING?
#  _temp/tested/slf18_two_dice.c \

MD = $(shell find docs -type f -name "*.md")
CONSISTENT=$(patsubst %, _temp/consistent/%, $(MD))

exercises: $(EXERCISES) $(SOLUTIONS) $(TESTED) $(VERIFIED) $(CONSISTENT)

CN=cn verify
CNTEST=cn test --output _temp

# Control verbosity (run make with V= to show everything that's happening)
V=@

# BCP: This is a temporary hack to use gcc to preprocess #includes
#      because CN doesn't handle them right.
_temp/tested/% : src/exercises/%
	$(V)echo Testing $<
	$(V)-mkdir -p $(dir $@)
	$(V)-mkdir -p $(dir _temp/$<.combined.c)
	$(V)gcc -E -CC  -P $<   > _temp/$<.combined.c
	$(V)$(CNTEST) _temp/$<.combined.c   2>&1 | tee $@.test.out
	$(V)-grep "PASSED\\|FAILED" $@.test.out || true
	@# Next line should not be needed!
	$(V)if grep -q "fatal error\\|Failed to compile\\|Failed to link\\|: error:" $@.test.out; then \
	      exit 1; \
	    fi
	$(V)touch $@

## BCP: Better version...
#
# _temp/tested/% : src/exercises/%
#	$(V)echo Testing $<
#	$(V)-mkdir -p $(dir $@)
#	$(V)$(CNTEST) $<   2>&1 | tee $@.test.out
#	$(V)-grep "PASSED\\|FAILED" $@.test.out || true
#	@# Next line should not be needed!
#	$(V)if grep -q "fatal error\\|Failed to compile" $@.test.out; then \
#               exit 1; \
#	    fi
#	$(V)touch $@

_temp/verified/% : src/exercises/%
	$(V)echo Verifying $<
	$(V)-mkdir -p $(dir $@)
	$(V)$(CN) $<   2>&1 | tee $@.verif.out
	$(V)if grep -q "fatal error\\|Failed to compile\\|Failed to link\\|: error:" $@.verif.out; then \
	      exit 1; \
	    fi
	$(V)touch $@

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

# cn test --output-dir=$(HOME)/tmp read.broken.c

# OLD
# docs/solutions/%: src/exercises/%
#	@-mkdir -p $(dir $@)
#	@-mkdir -p _tests
#	@if [ `which cn` ]; then \
#	  if [[ "$<" = *".c"* ]]; then \
#	    if [[ "$<" != *"broken"* && "$<" != *"partial"* && "$<" != *".DS_Store"* ]]; then \
#	      if [[ "$<" = *".test."*c ]]; then \
#		echo $(CNTEST) $< && $(CNTEST) $< --output _tests; \
#               else \
#		echo $(CN) $< && $(CN) $<; \
#	      fi; \
#             fi; \
#	  fi \
#	fi
#	@echo Rebuild $@
#	@cat $< | sed '\|^.*--BEGIN--.*$$|d' | sed '\|^.*--END--.*$$|d' > $@

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
# Check for inconsistent exercise names / paths

_temp/consistent/% : %
	$(V)perl -0777 -ne \
	   'while (/c title=\"(.+)\"\n.+\n(.+)\n/g) { \
	     if ($$1 ne $$2) { \
	       print "Bad .md file ($<): $$1 does not match $$2\n"; \
	       exit 1;  \
	   } }' \
	   $<
	$(V)-mkdir -p $(dir $@)
	$(V)touch $@

##############################################################################
# Tutorial document

tutorial: rebuild
	mkdocs build --strict

serve: rebuild
	mkdocs serve

rebuild: exercises docs/exercises.zip mkdocs.yml $(shell find docs -type f)

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
