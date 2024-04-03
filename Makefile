.PHONY: default clean

default: build build/tutorial.html

build:
	mkdir -p build
	mkdir -p build/exercises
	mkdir -p build/solutions

clean:
	rm -rf build

clean:
	rm -rf build

SRC_EXAMPLES=$(wildcard src/examples/*)
SOLUTIONS=$(patsubst src/examples/%, build/solutions/%, $(SRC_EXAMPLES))
EXERCISES=$(patsubst src/examples/%, build/exercises/%, $(SRC_EXAMPLES))



build/exercises/%: src/examples/%
	sed -E '/^--BEGIN--$$/,/^--END--$$/d' $< > $@

build/solutions/%: src/examples/%
	cat $< | sed '/^--BEGIN--$$/d' | sed '/^--END--$$/d' > $@


# build/tutorial.md: src/tutorial.md $(EXERCISES) $(SOLUTIONS)
# 	@echo $(EXERCISES)
# 	m4 -I build $< > $@

# build/tutorial.html: build/tutorial.md
# 	pandoc -t html5 \
# 	       --standalone \
# 		   --embed-resources \
# 		   --highlight-style=pygments \
# 		   --toc \
# 		$< -o $@


build/tutorial.adoc: src/tutorial.adoc
	cp $< $@

build/images: src/images
	cp -r $< $@

build/tutorial.html: build/tutorial.adoc $(EXERCISES) $(SOLUTIONS) build/images
	asciidoctor --doctype book $< -o $@
