CN Naming Conventions
---------------------

This document describes our (Benjamin and Liz's) current best shot at
a good set of conventions for naming identifiers in CN, based on
numerous discussions and worked examples.

All the list-related files in src/examples have been converted to this
convention -- do `ls src/examples/list*` to check it out.

# Principles

- When similar concepts exist in both C and CN, they should be named
  so that the correspondence is immediately obvious.
     - In particular, the C and CN versions of a given data structure
       should have very similar names.

- In text, we use the modifiers _CN-level_ vs. _C-level_ to
  distinguish the two worlds.

# General conventions

 ## For new code

When we're writing both C and CN code from scratch (e.g., in the
tutorial), we aim for maximal correspondence between 

- In general, CN identifiers are written in `snake_case` rather than `camlCase`

- C-level identifiers are `lowercase_consistently_throughout`

- CN-level identifiers are `Uppercase_Consistently_Throughout`

- A CN identifier that represents the state of a mutable data
  structure after some function returns should be named the same as
  the starting state of the data structure, with an `_post` at the
  end.
      - E.g., The list copy function takes a linked list `l`
        representing a sequence `L` and leaves `l` at the end pointing
        to a final sequence `L_post` such that `L == L_post`.
        (Moreover, it returns a new sequence `Ret` with `L == Ret`.)

- Predicates that extract some structure from the heap should be named
  the same as the structure they extract.  E.g., the result
  type of the `Queue` predicate is also called `Queue`.

  *Discussion*: There is clearly some potential for confusion, and for
  this reason Liz prefers using `Queue_at` for the predicate.  On the
  other hand hand, types don't take an argument and predicates do, so
  it's easy to disambiguate.  We're going with the lighter alternative
  for the moment.
  
## For existing code

In existing C codebases, uppercase-initial identifiers are often used
for typedefs, structs, and enumerations.  We should choose a
recommended standard convention for such cases -- e.g., "prefix
CN-level identifiers with `CN` when needed to avoid confusion with
C-level identifiers".  Some experimentation will be needed to see
which convention we like best; this is left for future discussions.

# Built-ins

This proposal may also require changing some built-ins for
consistency.

      - `i32` should change to `I32`, `u64` to `U64`
      - `is_null` to `Is_null` (or `Is_Null`)

*Discussion*: One point against this change is that CN currently tries
to use names reminiscent of Rust (`i32`, `u64`, etc.).  I (BCP) do not
personally find this argument persuasive -- internal consistency seems
more important than miscellaeous points of similarity with some other
language.  One way or the other, this will require a global decision.

# Polymorphism

One particularly tricky issue is how to name the "monomorphic
instances" of "morally polymorphic" functions (i.e., whether to write
`append__Int` or `append__List_Int` rather than just `append`).  On
one hand, `append__Int` is "more correct".  On the other hand, these
extra annotations can get pretty heavy.

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
   type definitions and library functions is *only used at one
   monomorphic instance* (e.g., if some codebase only ever uses lists
   of 32-bit signed ints), then the `__int` or `__I32` annotations are
   omitted.

   This convention is used in the CN tutorial, for example.

   TODO: Right now, the tutorial uses option (1).  It was this
   exercise that convinced me [BCP] that option (2) was better. :-)

*Discussion*: One downside of this convention is that it might
sometimes require some after-the-fact renaming: If a project starts
out using just lists of signed ints and later needs to introduce lists
of unsigned ints, the old signed operations will need to be renamed.
This seems like an acceptable cost for keeping things light.

Another downside is that it introduces two different ways of naming
polymorphic things.  But hopefully (a) the appropriate use of each is
clear and (b) most C developments will actually fall in the second,
lighter case, and programmers will never need to bother understanding
the first case.

# Loose ends

- Do we need a convention for auxiliary predicates?
    - E.g., maybe adding `_Aux` to the original predicate name
      (e.g. `Queue_Aux` for the recursive predicate that walks down
      the list of queue nodes to gather them into a list once a
      top-level `Queue` or `Queue_at` predicate has dealt with the
      non-recursive part of the structure).

- The current function `IntList_free__list` is hard to rename with
  these conventions. It feels like it should be `free__int_list`, but
  that’s also the new name of the free function for individual list
  cells (opposite of `malloc`). Current solution is
  `free_rec__int_list`.
    - BCP wonders if this issue is specific to malloc and free.  If
      so, maybe we can make some special convention like
      `free__int_list_node` for the single-node operation (even though
      what it returns is an `int_list`, noit an `int_list_node`),
      leaving `free__int_list` for the recursive one?
