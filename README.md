# CN-tutorial

In order to build the tutorial, you will first need to install [asciidoctor](https://asciidoctor.org/).

Run `make` to produce `build/tutorial.html` and its dependencies: especially, `build/exercises/*.c` and `build/solutions/*c`.

Run `./check.sh` to check that all examples have working solutions (except tests with names `*.error.c`, which are expected to fail). Note that this step will not work until after you have installed CN, which is the first part of the tutorial.
