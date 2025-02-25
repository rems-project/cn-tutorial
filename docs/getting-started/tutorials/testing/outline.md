# Outline of the New Testing Tutorial

## A proposed order of topics and examples...

- High-level overview of CN

- Hello world example of unit testing

- instructions for running unit tests themselves
    - an exercise to try it out on min3
    - an exercise to find a bug in a variant of min3
    - couple more (similar, optional) exercises

- Hello world example of PBT (min3)
    - original version:
      ```c title="exercises/min3/min3.orig.c"
      --8<--
      exercises/min3/min3-orig.c
      --8<--
      ```
    - with a specification:
      ```c title="exercises/min3/min3.test.c"
      --8<--
      exercises/min3/min3.test.c
      --8<--
      ```
    - with a spec and a mistake:
      ```c title="exercises/min3/min3.brokentest.c"
      --8<--
      exercises/min3/min3.brokentest.c
      --8<--
      ```

- instructions for running PBT themselves
    - an exercise to try it out on min3
    - an exercise to find a bug in a variant of min3
    - couple more (similar, optional) exercises -- e.g., sorting three
      numbers 

- Maybe some more examples of very simple C programs (no pointers, no
  UB, ...)

## Further Topics:

- How to write specs (a huge topic!)
- Testing programs with pointers (but not dynamic storage allocation)
- Testing array-manipulating code
- Testing heap-manipulating code (lists, etc.)
- Checking for UB
- Larger case studies

## Questions and TODOs

- Go through the verification tutorial and move some stuff here
- When do we introduce unit tests?  Can we do it at the very beginning?
    - I think yes, but the fulminate instructions are currently quite
      hard to follow!
- The makefile should confirm that broken tests actually fail
