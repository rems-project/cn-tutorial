# CN Tutorial

CN is an integrated specification, testing, and verification framework
for low-level software systems written in ISO C.

This tutorial introduces CN through a series of examples and case
studies, starting with basic usage of CN on simple arithmetic
functions and slowly moving towards more elaborate separation logic
specifications of data structures.
<!-- TODO: BCP: Once the structure of the tutorial stabilizes, we -->
<!-- could outline the material it covers in more detail... -->

CN can be used in two distinct ways.  The simpler usage is as a
framework for writing down formal specifications of C code, in the
form of logical pre- and post-conditions, and _testing_ that the code
agrees with the specification on specific examples. This usage mode
may be sufficient for many purposes.
- 


## Source files

The source files for all the exercises and examples below can be downloaded
from [here](link:exercises.zip).

## Tutorials

### Testing

- [Outline](testing/outline.md)
**More links needed here**

### Verification

- [Basic usage](verification/basic-usage.md)
- [Pointers and simple ownership](verification/pointers-and-simple-ownership.md)
- [Ownership of compound objects](verification/ownership-of-compound-objects.md)
- [Arrays and loops](verification/arrays-and-loops.md)
- [Defining predicates](verification/defining-predicates.md)
- [Allocating and deallocating memory](verification/allocating-and-deallocating-memory.md)
- [Lists](verification/lists.md)
- [Working with external lemmas](verification/external-lemmas.md)

## Case studies

- [Imperative queues](../case-studies/imperative-queues.md)
- [Doubly-linked lists](../case-studies/doubly-linked-lists.md)
- [Airport Simulation](../case-studies/the-runway.md)
