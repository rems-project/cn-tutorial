# CN Tutorial

View the tutorial here: https://rems-project.github.io/cn-tutorial/

## Building

Install dependencies: [asciidoctor](https://asciidoctor.org/).

Run `make` to produce `build/tutorial.html` and its dependencies: especially, `build/exercises/*.c` and `build/solutions/*c`.

Run `make check-tutorial` to check that all examples in the tutorial have working solutions (except tests with names `*.broken.c`, which are expected to fail). Note that this step will not work until after you have installed CN, which is the first part of the tutorial.

Run `make check` to checks both the tutorial and archive examples (see below). 

## CN Example Archive 

The subdirectory `src/example-archive` includes many more examples of CN proofs, both working and broken. See [the README](./src/example-archive/README.md) for a description how these examples are organized. 

Run `make check-archive` to check all examples in the example archive. 