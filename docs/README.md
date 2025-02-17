# Welcome to CN

_These tutorials and docs were developed by Christopher Pulte, Benjamin C.
Pierce, and Cole Schlesinger, with contributions from Elizbeth Austell._

??? info "BibTeX"
    ```
    @misc{cn-tutorial,
      author = {Christopher Pulte and Benjamin C. Pierce and Cole Schlesinger and Elizabeth Austell},
      title = {{CN Tutorial}},
      howpublished = "\url{https://rems-project.github.io/cn-tutorial/}",
      year = {2025},
    }
    ```

CN is an extension of the C programming language for testing and verifying the
correctness of C code, especially on low-level systems code. Compared to
standard C, CN checks not only that expressions and statements follow the
correct typing discipline for C-types, but also that the C code executes
_safely_ — does not raise C undefined behaviour — and _correctly_ — satisfying
to strong, user-defined specifications.

CN provides utilities for verifying specifications at compile time as well as
automatically generating unit and integration tests to test specifications at
runtime.

This documentation is a work in progress -- your suggestions are greatly
appreciated!

<div class="grid cards" markdown>

-   :material-clock-fast:{ .lg .middle } __Set up in 5 minutes__

    ---

    Build and install CN and get up and running in minutes

    [:octicons-arrow-right-24: Installing CN](getting-started/installation.md)

-   :fontawesome-brands-markdown:{ .lg .middle } __Your first spec__

    ---

    Check out the *Basic Usage* tutorial to write, test, and verify your first
    spec

    [:octicons-arrow-right-24: Basic Usage](getting-started/tutorials/verification/basic-usage.md)

-   :material-format-font:{ .lg .middle } __Tutorials__

    ---

    Find tutorials covering common tasks and introducing CN features

    [:octicons-arrow-right-24: Tutorials](getting-started/tutorials/README.md)

-   :material-scale-balance:{ .lg .middle } __Language reference__

    ---

    Quick reference for CN specification syntax

    [:octicons-arrow-right-24: Language reference](reference/README.md)

</div>

## Origins and papers
CN was first described in [CN: Verifying Systems C Code with Separation-Logic Refinement Types](https://dl.acm.org/doi/10.1145/3571194) by Christopher Pulte, Dhruv C. Makwana, Thomas Sewell, Kayvan Memarian, Peter Sewell, and Neel Krishnaswami, in POPL 2023.
The Fulminate system for runtime testing of CN specifications was first described in [Fulminate: Testing CN Separation-Logic Specifications in C](http://www.cl.cam.ac.uk/users/pes20/cn-testing-popl2025.pdf), by Rini Banerjee, Kayvan Memarian, Dhruv Makwana, Christopher Pulte, Neel Krishnaswami, and Peter Sewell, in POPL 2025.
To accurately handle the complex semantics of C, CN builds on the [Cerberus semantics for C](https://github.com/rems-project/cerberus/).
Some of the examples in this tutorial are adapted from Arthur Charguéraud’s excellent
[Separation Logic Foundations](https://softwarefoundations.cis.upenn.edu) textbook, and one of the case studies is based on an
extended exercise due to Bryan Parno.

## Acknowledgment of Support and Disclaimer
This material is based upon work supported by the Air Force Research Laboratory (AFRL) and Defense Advanced Research Projects Agencies (DARPA) under Contract No. FA8750-24-C-B044, a European Research Council (ERC) Advanced Grant “ELVER” under the European Union’s Horizon 2020 research and innovation programme (grant agreement no. 789108), and additional funding from Google. The opinions, findings, and conclusions or recommendations expressed in this material are those of the authors and do not necessarily reflect the views of the Air Force Research Laboratory (AFRL).

## Building these docs

These docs are built with [Material for
MkDocs](https://squidfunk.github.io/mkdocs-material/).  To build and serve them
locally on http://localhost:8000:

```bash
# Install Material for MkDocs
pip install mkdocs-material

# In the cn-tutorial root directory, run
mkdocs serve
```

## Docs layout

    mkdocs.yml    # The configuration file.
    docs/
        README.md # The documentation homepage.
        ...       # Other markdown pages, images and other files.
