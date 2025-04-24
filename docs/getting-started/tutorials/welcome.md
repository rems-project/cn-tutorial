# Welcome

## Introduction

CN is an integrated specification, testing, and verification framework
for low-level software systems written in ISO C.

This tutorial introduces CN through a series of examples and case
studies, starting with basic usage of CN on simple arithmetic
functions and slowly moving towards more elaborate separation logic
specifications of data structures.
{{ later("BCP: Once the structure of the tutorial stabilizes, we
     could outline the material it covers in more detail...") }}

CN can be used in two distinct ways:

- The simpler way is as a framework for writing down formal
  specifications of C code, in the form of logical pre- and
  post-conditions, and _testing_ that the code agrees with its
  specification on specific examples. This is sufficient for many
  purposes.
- The more sophisticated way is as a framework for _proving_ that C
  programs agree with their specifications.  This gives a higher level
  of assurance, in return for a somewhat larger investment in learning
  to use the verification-oriented aspects of CN.

The main thread of this tutorial is aimed at readers who want to get up to speed
quickly with specifying and testing C programs using CN. Verification topics are
covered in optional sections whose names are _italicized_. Most
readers — even readers whose
primary interest is verification — should skip these sections on a first reading
and, if desired, come back to them on a second pass.

## Setup instructions

Before getting started, make sure you have a running installation of
CN and a local copy of the source files for all the exercises and
examples; these can be downloaded from [here](link:exercises.zip).

## Acknowledgment of support and disclaimer

This material is based upon work supported by the Air Force Research
Laboratory (AFRL) and Defense Advanced Research Projects Agencies
(DARPA) under Contract No. FA8750-24-C-B044, a European Research
Council (ERC) Advanced Grant “ELVER” under the European Union’s
Horizon 2020 research and innovation programme (grant agreement
no. 789108), and additional funding from Google. The opinions,
findings, and conclusions or recommendations expressed in this
material are those of the authors and do not necessarily reflect the
views of AFRL or DARPA.
