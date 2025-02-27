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
     - use unsigned arithmetic, to avoid UB!  (This would be good in
       the verification tutorial too!)

- Testing programs with pointers (but not dynamic storage allocation)

    - read.c
        - unannotated version fails tests 
             - need to explain how to figure out WHY testing fails!
        - explain ownership (copy/move from verification tutorial)
        - version with proper spec works better!
        - (lots of useful text)
        - read.broken.c demonstrates linearity of resource usage
    - exercises:
        - quadruple_mem
        - abs_mem
    - slf0_basic_incr_signed.c
        shows the difference between Block and Owned
    - exercises
        - zero.c
        - basic_inplace_double.c involves UB, so skip?
        - maybe something about swapping pointers?

    - add_read  (but changing it to swapping or something, to avoid UB
      issues) 

    - everything up through pointers to compound objects seems to work
      well, except for some of the resource inference stuff

## Further Topics:

- How to write specs (a huge topic!)
- Numeric types, conversions, overflow, etc.
    - abs.c is a good exercise (probably we'd just move it entirely,
      along with the paragraph above it)
- Testing array-manipulating code
- Testing heap-manipulating code (lists, etc.)
- Checking for UB
     - Note that the verification tutorial *begins* with an example that
       testing doesn't handle at all!
- Larger case studies

## Questions and TODOs

- Go through the verification tutorial and move some stuff here
- When do we introduce unit tests?  Can we do it at the very beginning?
    - I think yes, but the fulminate instructions are currently quite
      hard to follow!
- The makefile should confirm that broken tests actually 
- VSCode / Copilot gives a lot of hints (some correct)!!
- The naming of exercises is hideous (esp. the slf ones)
- Starting with signed overflow, etc., is horrible
- I think the verification material can be organized so that it can be
  read either interleaved with the testing tutorial or completely
  after it.

## CN / VSCode Nits
- It would be nice if (a) errors were indicated more boldly (e.g., a
  red slug in the margin, not just red squiggles) and (b) successful
  verification were visually indicated somehow (green light goes on,
  or whatever).
