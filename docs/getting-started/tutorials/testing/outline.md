# Introduction

- High-level overview of CN

- Overview of this tutorial; road map; what you're going to learn; how
  to approach the document, depending on your goals
     - "I want to improve the coverage of my tests"
     - "I want to learn how to verify C code"
     - ...

# Unit Testing

(BCP: I'd like to introduce unit testing at the very start, but the
Fulminate instructions are currently quite hard to follow!  (When) can
we improve that?)

(We may actually want to go straight to PBT long term, because unit
testing will be integrated with build systems, unit testing
infrastructure, etc., so more complicated to set up.  Hard to predict
exactly how this will look as we scale.)

- Hello-world example of unit testing

- instructions for running unit tests themselves
    - an exercise to try it out on min3
    - an exercise to find a bug in a variant of min3
    - couple more (similar, optional) exercises

TODO: Complete instructions for running Fulminate on the min3 example.

# PBT

- Hello-world example of PBT (min3)
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

- instructions for running PBT
    - an exercise to try it out on min3
    - an exercise to find a bug in a variant of min3
    - couple more (similar, optional) exercises -- e.g., sorting three
      numbers

- Some more examples of very simple C programs
     - use unsigned arithmetic in all the early sections to avoid UB!
     - (convert all the existing examples and exercises to unsigned,
       leaving signed arithmetic and UB to a later section by
       themselves)

[BCP: In the rest of the tutorial, maybe we could be agnostic
(somewhat agnostic, at least) about whether people are using unit
tests or PBT.  I don't have a sense yet of whether that will really
work, but it would have the good effect of focusing everybody's
attention on specifications and how to think about them, rather than
the testing process itself.]

Throughout, we want several sorts of exercises:
- Here's the code; write a spec; now here's a broken version of the
  code - does your spec catch it?
- Here's the code; write and validate a spec by breaking it yourself
- Here's a spec; write the program
- Here are requirements (with or without test cases); write the spec
  and the code

# Programs with Pointers

(but not yet dynamic storage allocation)

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

## Arrays

## Dynamic Heap Structures

## Numeric Types

- Signed numeric types, sizes, conversions, overflow, etc.
    - abs.c is a good exercise (probably we'd just move it entirely,
      along with the paragraph above it)
    - Checking for UB
         - Note that the verification tutorial *begins* with an example that
           testing doesn't handle at all!

## Case studies

Case studies drawn from the SUT(s), focused on specs
    - e.g., system never enters bad state
    - e.g., code mimics a state machine

Explicit chapters / case studies on each of the "high-value" PBT
situations that Harry identified in the Jane Street study
    - simple memory safety specs
    - other simple symbolic sanity-check properties
    - round-trip properties
    - model implementations

The current case studies from the verification tutorial
  - make a testing variant and an optional verification variant of
    each of them

____________________________________________________________________

# Questions and Discussion Points

- The naming of exercises is hideous (esp. the slf ones)

- I (bcp) am now leaning toward making the verification material
  mostly be extra optional sections that users can read after each
  major section of the testing tutorial -- i.e., it's not two separate
  tutorials, but rather one tutorial with a bunch of sections that
  people can skip if they only care about testing. This works because
  the main focus of the testing parts is actually not testing, but
  rather _specification_. (By contrast, the verification parts really
  do have to talk quite a bit about the process of verification
  itself, because verification is hard and there's a lot to say.)

- We should think of / coin a word or phrase that means "unit testing,
  but with a specification that tells you whether the system produced
  the right answer, rather than an explicitly (programmer-)provided
  expected output."  E.g., maybe "unit testing with an oracle"?  (OK,
  but the person on the street will not know what we mean by oracle in
  this context.)

- The makefile should confirm that broken tests actually break

____________________________________________________________________

# CN / VSCode Nits
- It would be nice if (a) errors were indicated more boldly (e.g., a
  red slug in the margin, not just red squiggles) and (b) successful
  verification were visually indicated somehow (green light goes on,
  or whatever).
- VSCode with Copilot currently gives a *lot* of hints (some correct)!!
- One could imagine that users would sometimes want *both* unit tests
  and PBT.  E.g., if the PBT generator is having trouble hitting some
  parts of the code, they could be covered by hand-written tests.  Or
  maybe people start by writing unit tests and later add PBT; it would
  be silly to *not* run the unit tests they've written.
