# Working with External Lemmas

{{ todo("BCP: This section should also show what the proof of the lemmas
looks like on the Coq side! ") }}

{{ todo("BCP: This needs to be filled in urgently!! ") }}
{{ todo(" Dhruyv: There are some examples in the Cerberus repo tests? rems-project/cerberus@20d9d5c ") }}

{{ todo("BCP:
think about capitalization, etc., for lemma names
push_lemma should be Push_lemma, I guess? Or lemma_push?
snoc_facts should be lemma_Snoc or something
others?") }}

### List reverse

The specification of list reversal in CN relies on the familiar
recursive list reverse function, with a recursive helper.

```c title="exercises/list/snoc.h"
--8<--
exercises/list/snoc.h
--8<--
```

```c title="exercises/list/rev.h"
--8<--
exercises/list/rev.h
--8<--
```

To reason about the C implementation of list reverse, we need to help
the SMT solver by enriching its knowledge base with a couple of facts
about lists. The proofs of these facts require induction, so in CN we
simply state them as lemmas and defer the proofs to Coq.

```c title="exercises/list/rev_lemmas.h"
--8<--
exercises/list/rev_lemmas.h
--8<--
```

Having stated these lemmas, we can now complete the specification and
proof of `IntList_rev`. Note the two places where `apply` is used
to tell the SMT solver where to pay attention to the lemmas.

{{ todo("BCP: Why can't it always pay attention to them? (I guess
'performance', but at least it would be nice to be able to declare a
general scope where a given set of lemmas might be needed, rather than
specifying exactly where to use them.)") }}

```c title="exercises/list/rev.c"
--8<--
exercises/list/rev.c
--8<--
```

For comparison, here is another way to write the program, using a
while loop instead of recursion, with its specification and proof.

{{ todo("BCP: Why 0 instead of NULL?? (Is 0 better?) ") }}

```c title="exercises/list/rev_alt.c"
--8<--
exercises/list/rev_alt.c
--8<--
```

### Exercises

**Sized stacks:** Fill in annotations where requested:

{{ todo("BCP: type_synonym has not been introduced yet ") }}

```c title="exercises/slf_sized_stack.c"
--8<--
exercises/slf_sized_stack.c
--8<--
```

{{ todo(" ====================================================================== ") }}



## More on CN Annotations

{{ todo("Introduce all the different sorts of CN annotations (e.g.,
  `split_case`) individually with small examples and exercises.") }}


