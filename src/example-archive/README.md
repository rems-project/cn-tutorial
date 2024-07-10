This directory contains examples for CN. Each subdirectory contains examples from one source. 

## Current example sources

* `simple-examples` - Many small examples showing off individual CN features and
  reasoning patterns.
* `c-testsuite` - Examples from the [`c-testsuite`](https://github.com/c-testsuite/c-testsuite) database of C compiler tests. 
* `dafny-tutorial` - Examples constructed by following the Dafny tutorial
  [here](https://dafny.org/dafny/OnlineTutorial/guide.html).
* `Rust` - C versions of Rust programs, with CN annotations that provide the same guarantees as the Rust type-checker.
* `SAW` - Examples derived from the [Software Analysis Workbench (SAW)](https://saw.galois.com) repository and tutorial. 
* `open-sut` - Examples inspired by the VERSE Open System Under Test (Open SUT).
* `coq-lemmas` - Examples with declared lemmas that can be exported to Coq for manual proofs.

## Organization  

Examples from a single source are stored in a single subdirectory. The examples
are categorized according to the following schema. 

* `<source>/README.md` - documents the source of the examples and any license. 
* `<source>/working` - examples that CN verifies without error. 
* `<source>/broken/error-cerberus` - examples where CN fails with error 2,
  indicating a Cerberus error. 
* `<source>/broken/error-crash` - examples where CN crashes with error 125, and
  generates a stack trace. 
* `<source>/broken/error-proof` - examples where CN fails with error 1,
  indicating the proof failed. 
* `<source>/broken/error-timeout` - examples where CN times out after 60s. 
* `<source>/coq/*` - examples that CN verifies without error and have lemmas that should be extracted. According to the following rules
    * `<source>/coq/working` - Examples where Coq lemmas can be extracted and the Coq project can be built.
    * `<source>/coq/broken-build` - Examples where Coq lemmas can be extracted, but the Coq build process fails.
    * `<source>/coq/broken-export` - Examples where Coq extraction fails. These should still be verifiable with CN.
* `<source>/coq/working` - examples that CN verifies without error. 
* `<source>/inprogress` - unfinished examples. 

## Check script

To confirm that examples have been correctly categorized, you can use the `check.sh` shell script as follows: 
```
$ cd <subdirectory>
$ sh ../check.sh
``` 
