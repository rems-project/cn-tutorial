CN Naming Conventions
---------------------

At the moment, the way things are named in CN examples is all over the
map, leading to considerable friction and frustration.  We should
agree on some conventions that we like, do one painful global rename
to change everything in the tutorial (at least) to use them, and then
stick to them for new stuff we write.

This document describes our (Benjamin and Liz's) best shot at a good
set of conventions, based on past discussions.

All the list-related files in src/examples have been converted to this
convention -- do `ls src/examples/{list*,Seq*}` to check it out.


## Code conventions

Rules:
    - In general, identifiers are written in `snake_case` rather than `camlCase`
    - C-level identifiers are `lowercase_initial`
    - CN-level identifiers are `Uppercase_initial`
    - Polymorphic functions and predicates, at both C and CN levels, are
      "monomorphized" by adding their type arguments at the end,
      connected by `__`
          - E.g., `queue__int`
    - When the same concept exists at both the C and CN levels, it is
      named the same except for the lowercase/uppercase distinction
          - E.g., `queue__int` at the C level vs. `Queue__I32` at the
            CN level
          - When a single structure at the CN level is used to talk
            about many different structures at the C level -- e.g.,
            mathematical sequences are the abstract content of many
            concrete heap data structures (lists, doubly linked lists,
            queues, ...), the CN structure should have a name that
            distinguishes it from all the concrete realizations.  In
            particular, the type of mathematical lists is called
            `Seq__U32`, not `List__U32`.
               - Alternatively, we could rename `Seq` back to `List`
                 but then use `linked_list__int` instead of just
                 `list__int` at the C level.
    - A CN identifier that represents the state of a mutable data
      structure when some function returns should be named the same as
      the starting state of the data structure, with an `_` at the
      end.
          - E.g., The list copy function takes a linked list `l`
            representing a sequence `L` and leaves `l` pointing to a
            final sequence `L_` such that `L == L_`.  Moreover, it
            returns a new sequence `Ret` with `L == Ret`.

Questions / concerns / ideas:
    - Should CN-level identifiers be `Uppercase_initial` or
      `Uppercase_Consistently_Throughout`?  I [BCP] find the latter a
      bit lighter.
    - Convention for naming predicates?
          - One suggestion is the suffix `_at` to represent the
            assertion that there is an object at that address. For
            example, `Queue_U32_at(p)`.
    - Convention for auxiliary predicates?
          - Maybe adding `_Aux` to the original predicate name
            (e.g. `Queue_U32_at_Aux`).
    - Does capitalization convention apply to function names?
      Ex. `list_int_copy()` vs `List_Int_Copy()`. The list_int is in C so it
      should be lowercase, but is that true for the name of a function
      that affects it?
          - (BCP: Don't understand this one?)
    - The existing function `IntList_free_list` is hard to rename with
      these conventions. It feels like it should be `free_int_list`,
      but that’s also the new name of the free function for individual
      list cells (opposite of `malloc`). Current solution is
      `free_int_list_rec`.

Notes:
    - This proposal will also require changing some built-ins if we really
      take it seriously
          - `i32` to `I32`, `u64` to `U64`
          - `is_null` to `Is_null` (or `Is_Null`)

## Text conventions

Rules:
    - Consistently use the word "abstract" to refer to CN-level
      ("mathematical") structures
          - Would _specification-level_ be better than "abstract"
            (i.e., clearer, even if it a bit clunkier)?
    - Consistently use the word "concrete" to refer to C-level
      structures on the stack/heap
          - Would _implementation-level_ be better than "concrete"?
