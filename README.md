# CN-tutorial

In order to build the tutorial, you will first need to install [asciidoctor](https://asciidoctor.org/).

Run `make` to produce `build/tutorial.html` and its dependencies: especially, `build/exercises/*.c` and `build/solutions/*c`.

Run `./check.sh` to check that all examples have working solutions (except tests with names `*.broken.c`, which are expected to fail). Note that this step will not work until after you have installed CN, which is the first part of the tutorial.

## CN Example Archive 

The subdirectory `src/example-archive` includes many more examples of CN proofs, both working and broken. See [the README](./src/example-archive/README.md) for a description how these examples are organized and instructions for running CN on them. 
