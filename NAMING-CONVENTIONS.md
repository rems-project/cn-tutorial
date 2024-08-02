CN Naming Conventions
---------------------

This document describes our (Benjamin and Liz's) best shot at a good
set of conventions for naming identifiers in CN, based on numerous
discussions and worked examples.

All the list-related files in src/examples have been converted to this
convention -- do `ls src/examples/list*` to check it out.

# General Conventions

- In general, identifiers are written in `snake_case` rather than `camlCase`

- C-level identifiers are `lowercase_initial`

- CN-level identifiers are `Uppercase_initial`

- A CN identifier that represents the state of a mutable data
  structure after some function returns should be named the same as
  the starting state of the data structure, with an `_` at the
  end.
      - E.g., The list copy function takes a linked list `l`
        representing a sequence `L` and leaves `l` at the end pointing
        to a final sequence `L_` such that `L == L_`.  (Moreover, it
        returns a new sequence `Ret` with `L == Ret`.)

## Questions:

- Should CN-level identifiers be `Uppercase_initial` or
  `Uppercase_Consistently_Throughout`?

  BCP find the former a bit lighter.  Liz finds the latter to be more
  consistent. If `List_int` is the identifier and `Rev_list_int` is
  the function, then `list_int` is lowercase in the function even
  though it is usually capital.  (BCP admits this is a fair point.)
  What do others think?

- Should predicates that extract some structure from the heap be named
  the same as the structure they extract.  I.e., should the result
  type of the `Queue` predicate also be called `Queue`?

  On one hand, there is clearly some potential for confusion.  On the
  other hand, types don't take an argument and predicates do, so it's
  easy to disambiguate.

  On balance, I [BCP] prefer naming both the same; Liz prefers using
  `Queue_at` for the predicate.

# Built-ins

- This proposal will also require changing some built-ins if we really
  take it seriously
      - `i32` should change to `I32`, `u64` to `U64`
      - `is_null` to `Is_null` (or `Is_Null`)

# Polymorphism

How to name the "instances" of "morally polymorphic" functions (i.e.,
should we write (i.e., whether to write `append__Int` or
`append__List_Int` rather than just `append`) is a tricky issue.  On
one hand, `append__Int` is "more correct".  On the other hand, these
extra annotations get pretty heavy.

We propose a compromise:

1. If a project needs to use two or more instances of some polymorphic
   type, then the names of the C and CN types, the C and CN functions
   operating over them, and the CN predicates describing them are all
   suffixed with `__xxx`, where `xxx` is the appropriate "type
   argument".  E.g., if some codebase uses lists of both signed and
   unsigned 32-bit ints, then we would use names like this:
      - `list__int` / `list__uint`
      - `append__int` / `append__uint`
      - `List__I32` / `List__U32`
      - `Cons__I32` / `Cons__U32`
      - etc.

2. However, if, in a given project, a set of "morally polymorphic"
   type definitions and library functions is only used at one
   monomorphic instance (e.g., if some codebase only ever needs lists
   of 32-bit signed ints), then the `__int` or `__I32` annotations are
   omitted.

   This convention should be used in the CN tutorial, for example.

   TODO: Right now, the tutorial uses option (1).  It was this
   exercise that convinced me [BCP] that option (2) was better. :-)

## Discussion

One downside of this convention is that it might sometimes require
some after-the-fact renaming: If a project starts out using just lists
of signed ints and later needs to introduce lists of unsigned ints,
the old signed operations will need to be renamed.  This seems like an
acceptable cost for keeping things light.

Another downside is that it introduces two different ways of naming
polymorphic things.  But hopefully (a) the appropriate use of each is
clear and (b) most C developments will actually fall in the second,
lighter case, and programmers will never need to bother understanding
the first case.

# Text conventions

We need some consistent way of distinguishing "C-level" things from
"CN-level" things.  Here are some possibilities:

1. _abstract_ for CN-level ("mathematical") structures vs. _concrete_
   for C-level structures

2. _specification-level_ vs. _implementation-level_

3. _CN-level_ vs. _C-level_

BCP thinks he likes the third best. Liz thinks all of these are good
options, but the first one communicates reality the most.  What about
you?

# Loose ends

- Do we need a convention for auxiliary predicates?
    - E.g., maybe adding `_Aux` to the original predicate name
      (e.g. `Queue_Aux` for the recursive predicate that walks down
      the list of queue nodes to gather them into a list once a
      top-level `Queue` or `Queue_at` predicate has dealt with the
      non-recursive part of the structure).

- The current function `IntList_free_list` is hard to rename with
  these conventions. It feels like it should be `free__int_list`, but
  that’s also the new name of the free function for individual list
  cells (opposite of `malloc`). Current solution is
  `free_rec__int_list`.
    - BCP wonders if this issue is specific to malloc and free.  If
      so, maybe we can make some special convention like
      `free__int_list_node` for the single-node operation (even though
      what it returns is an `int_list`, noit an `int_list_node`),
      leaving `free__int_list` for the recursive one?
