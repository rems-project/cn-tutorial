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
#if !CN_MUTATE_function_containing_the_mutantion_block
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


Notation for Unit Tests
=======================

Unit tests are written as CPP conditionals where the condition is
an identifier that starts with `CN_TEST_` followed by the
name of the function for the test.  For example:

```
#if CN_TEST_function_name
void function_name() {
  write test here
}
#endif
```

Sometimes we'd also like to indicate that a test is expected to fail. We can
do this by adding `// fails` on the line declaring the test.

```
#if CN_TEST_function_name // fails
void function_name() {
  write test here
}
#endif
```

This indicates that we expect this test to fail.


Scripts
=======

The directory also contains some scripts which use the preprocessor to run
the test variations in a file:

  * `run-all CFILE [LOG_FILE]`
     Test all functions in a file, including unit tests, and mutants.
     If a LOG_FILE is provided the output of the commands is stored
     there.  This is useful if tests fails.
     Mutants are considered to succeed if the corresponding test fails
     (i.e., they found a bug)
     Unit tests succeed if the result of testing matches the declarations
     (see `// fails` above)

  * `config` is a script fragment which defines the locations of external
     tools

  * `run-cn-test` is a script fragment which defines how we run CN tests

  * `run-unit` can run a single unit test.
     It just runs the unit test, without checking the expected outcome.

  * `run-mutant` can run a single mutation.

  * `run-prop-tests` test all "normal" functions (i.e., not unit tests or
    mutants)



