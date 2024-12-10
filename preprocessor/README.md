Overview
========

This is a small tool for pre-processing the example files in the tutorial.

We would like to ensure that CN's testing infrastructure works well with the
files in the tutorial, and so it is convenient to add additional annotations
to the files to support:
    * mutation testing, to ensure that property based testing is catching
      mistakes
    * custom unit test entry points, to ensure that executing specificatoins
      works as expected.

Both of these could, in principle, be useful to end user of CN, but for
tutorial purposes it is also conveninet to be able to remove these before
showing the files for the users.

This preprocessor is intended to help with this task.
To build it run `make`, and optionally `make clean`.  The result
should be an executable called `preproc_tut`.

Run `preproc_tut --help` to see a list of available commands.


Notation for Mutation Testing
=============================

The pre-processor is line based.  For mutation testing we use a CPP-like
if-block, as illustrated by the following example:
```
#if !MUTATION
Normal
code
path
#elif MutationName
Code for
some
mutation
#elif AnotherMutationName
Some other variant
#endif
```


If we run the pre-processer to eliminate mutation testing the result would
be only:

```
Normal
code
path
```


If we run the pre-processort to generate input for the Etna mutation testing
tool, we'd get:

```
//! //
Normal
code
path
//!! MutationName // //!
Code for
some
mutation
// //!! AnotherMutationName // //!
Some other variant
//
```


Unit Tests
==========

Unit tests are written as CPP conditionals where the condition is
an identifier that starts with `CN_TEST`.  For example:

```
#if CN_TEST
Lines only
for test
#endif
```
