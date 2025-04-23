# CN Tutorial

View the tutorial here: https://rems-project.github.io/cn-tutorial/

## Acknowledgment of Support and Disclaimer

This material is based upon work supported by the Air Force Research Laboratory
(AFRL) and Defense Advanced Research Projects Agencies (DARPA) under Contract
No. FA8750-24-C-B044, a European Research Council (ERC) Advanced Grant “ELVER”
under the European Union’s Horizon 2020 research and innovation programme
(grant agreement no. 789108), and additional funding from Google. The opinions,
findings, and conclusions or recommendations expressed in this material are
those of the authors and do not necessarily reflect the views of the Air Force
Research Laboratory (AFRL).

## Building

The CN tutorial is built using [Material for
MkDocs](https://squidfunk.github.io/mkdocs-material/).

Dependencies:
* python >=3.10

A suitable Python virtual environment can be created by running:

```console
> scripts/setup_env.sh
```

This script only needs to be run once.

It will create a `.venv/` with the dependencies necessary to build the CN
tutorial, which can be activated with:

```console
> source .venv/bin/activate
```

From here, building the tutorial is straightforward:

```console
> make
```

If you are _developing_ tutorial documentation, you may wish to include
developer commentary in the generated output.
To do so, simply set the `TUTORIAL_TODOS` environment variable (the value is
unimportant, so the empty string will suffice):

```bash
# Build the tutorial, including any developer comments
TUTORIAL_TODOS= make
```

Running `deactivate` will "turn off" the virtual environment; it can be
reactivated any time using the above `source .venv/bin/activate` command.

### Hosting locally

You can start a local server that automatically renders changes to the tutorial
files.  This is useful while editing the tutorial.

```bash
# Run the docs locally
make serve
```

(You can set `TUTORIAL_TODOS` as above to include developer commentary in served
documentation, i.e. `TUTORIAL_TODOS= make serve`.)

View at: http://localhost:8000/

Install dependencies: [asciidoctor](https://asciidoctor.org/).

## Tutorial examples

The tutorial examples live in [src/exercises](./src/exercises).

As part of building the tutorial, the examples are lightly preprocessed to
produce solutions and exercises (solutions with the CN specifications removed).

Run `make exercises` to produce the exercises and solutions in the `docs`
directory.

### Testing the tutorial examples

Follow these steps `make check-tutorial` to check that all examples in the tutorial have working solutions (except tests with names `*.broken.c`, which are expected to fail).

1. Install CN (follow steps in [the tutorial](https://rems-project.github.io/cn-tutorial/
))
2. Run `make check-tutorial`

## CN example archive 

The subdirectory `src/example-archive` includes many more examples of CN proofs, both working and broken. See [the README](./src/example-archive/README.md) for a description how these examples are organized. 

Install CN and run `make check-archive` to check all examples in the example archive. 
