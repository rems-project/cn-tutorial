# CN Tutorial

<span style="color:red">*Temporary -- stuff is moving to other files...*</span>

## PBT

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

- The Makefile should confirm that broken tests actually break

- The Makefile seems to build two copies of the examples (one in
  /build, one in /docs).  Is this optimal?

- Throughout, we want several sorts of exercises:
    - Here's the code; write a spec; now here's a broken version of the
      code - does your spec catch it?
    - Here's the code; write and validate a spec by breaking it yourself
    - Here's a spec; write the program
    - Here are requirements (with or without test cases); write the spec
      and the code

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

