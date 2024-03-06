.PHONY: default clean

default: build/tutorial.html

clean:
	rm -rf build/*
	mkdir build/exercises
	mkdir build/solutions

SRC_EXAMPLES=$(wildcard src/examples/*)
SOLUTIONS=$(patsubst src/examples/%, build/solutions/%, $(SRC_EXAMPLES))
EXERCISES=$(patsubst src/examples/%, build/exercises/%, $(SRC_EXAMPLES))



build/exercises/%: src/examples/%
	sed -E '/^--BEGIN--$$/,/^--END--$$/d' $< > $@

build/solutions/%: src/examples/%
	cat $< | sed '/^--BEGIN--$$/d' | sed '/^--END--$$/d' > $@


build/tutorial.md: src/tutorial.md $(EXERCISES) $(SOLUTIONS)
	@echo $(EXERCISES)
	m4 -I build $< > $@

build/tutorial.html: build/tutorial.md
	pandoc -t html5 \
	       --standalone \
		   --embed-resources \
		   --highlight-style=pygments \
		   --toc \
		$< -o $@
