# Airport Simulation, Verified

{{ todo("BCP: I'm nervous about this case study -- it is not nearly as well debugged as the others, and it seems potentially quite confusing. I propose deleting it, but if other like it we can try to whip it into better shape... ") }}

Suppose we have been tasked with writing a program that simulates a
runway at an airport. This airport is very small, so it only has one
runway, which is used for both takeoffs and landings. We want to
verify that the runway is always used safely, by checking the
following informal specification:

1. The runway has two modes: departure mode and arrival mode. The two
modes can never be active at the same time. Neither mode is active
at the beginning of the day.
{{ todo("BCP: Would it be simpler to say it is in arrival mode at the beginning of the day? What difference would that make? (Saying there are two modes and then immediately introducing a third one is a bit confusing.) ") }}

2. At any given moment, there is a waiting list of planes that need to
   land at the airport and planes that need to leave the
   airport. These are modeled with counters `W_A` for the number of
   planes waiting to arrive, and `W_D` for the number of planes
   waiting to depart.

3. At any moment, a plane is either waiting to arrive, waiting to
   depart, or on the runway. Once a plane has started arriving or
   departing, the corresponding counter (`W_A` or `W_D`) is
   decremented. There is no need to keep track of planes once they
   have arrived or departed. Additionally, once a plane is waiting to
   arrive or depart, it continues waiting until it has arrived or
   departed.

4. It takes 5 minutes for a plane to arrive or depart. During these 5
   minutes, no other plane may use the runway. We can keep track of
   how long a plane has been on the runway with the
   `Runway_Counter`. If the `Runway_Counter` is at 0, then there is
   currently no plane using the runway, and it is clear for another
   plane to begin arriving or departing. Once the `Runway_Counter`
   reaches 5, we can reset it at the next clock tick. One clock tick
   represents 1 minute.

5. If there is at least one plane waiting to depart and no cars
   waiting to arrive, then the runway is set to departure mode (and
   vice versa for arrivals).

6. If both modes of the runway are inactive and planes become ready to
   depart and arrive simultaneously, the runway will activate arrival
   mode first. If the runway is in arrival mode and there are planes
   waiting to depart, no more than 3 planes may arrive from that time
   point. When either no more planes are waiting to arrive or 3 planes
   have arrived, the runway switches to departure mode. If the runway
   is on arrival mode and no planes are waiting to depart, then the
   runway may stay in arrival mode until a plane is ready to depart,
   from which time the 3-plane limit is imposed (and vice versa for
   departures). Put simply, if any planes are waiting for a mode that
   is inactive, that mode will become active no more than 15 minutes
   later (5 minutes for each of 3 planes).

To encode all this in CN, we first need a way to describe the state of
the runway at a given time. We can use a _struct_ that includes the
following fields:

- `ModeA` and `ModeD` to represent the arrival and departure modes,
  respectively. We can define constants for `ACTIVE` and `INACTIVE`,
  as described in the `Constants` section above.

- `W_A` and `W_D` to represent the number of planes waiting to arrive
  and depart, respectively.

- `Runway_Time` to represent the time (in minutes) that a plane has
  spent on the runway while arriving or departing.

- `Plane_Counter` to represent the number of planes that have arrived
  or departed while planes are waiting for the other mode. This will
  help us keep track of the 3-plane limit as described in _(6)_.

```c title="exercises/runway/state.h"
--8<--
exercises/runway/state.h
--8<--
```

Next, we need to specify what makes a state valid. We must define a
rigorous specification in order to ensure that the runway is always
safe and working as intended. Try thinking about what this might look
like before looking at the code below.

```c title="exercises/runway/valid_state.h"
--8<--
exercises/runway/valid_state.h
--8<--
```

Let's walk through the specifications in `valid_state`:

- The first two lines ensure that both modes in our model behave as intended: they can only be active or inactive. Any other value for these fields would be invalid.

- The third line says that either arrival mode or departure mode must be inactive. This specification ensures that the runway is never in both modes at the same time.

- The fourth line says that the number of planes waiting to arrive or depart must be non-negative. This makes sense: we can't have a negative number of planes!

- The fifth line ensures that the runway time is between 0 and 5. This addresses how a plane takes 5 minutes on the runway as described in _(4)_.

- The sixth line ensures that the plane counter is between 0 and 3. This is important for the 3-plane limit as described in _(6)_.

- The seventh line refers to the state at the beginning of the day. If both modes are inactive, then the day has just begun, and thus no planes have departed yet. This is why the plane counter must be 0.

- The eighth line says that if there is a plane on the runway, then one of the modes must be active. This is because a plane can only be on the runway if it is either arriving or departing.

- The final two lines ensure that we are incrementing `Plane_Counter` only if there are planes waiting for the other mode, as described in _(6)_.

Now that we have the tools to reason about the state of the runway formally, let's start writing some functions.

First, let's look at an initialization function and functions to update `Plane_Counter`. Step through these yourself and make sure you understand the reasoning behind each specification.

```c title="exercises/runway/funcs1.h"
--8<--
exercises/runway/funcs1.h
--8<--
```

_Exercise_: Now try adding your own specifications to the following
functions. Make sure that you specify a valid state as a pre- and
post-condition for every function. If you get stuck, the solution is
in the solutions folder.

```c title="exercises/runway/funcs2.c"
--8<--
exercises/runway/funcs2.c
--8<--
```

<!-- ====================================================================== -->

## Acknowledgment of Support and Disclaimer

This material is based upon work supported by the Air Force Research Laboratory (AFRL) and Defense Advanced Research Projects Agencies (DARPA) under Contract No. FA8750-24-C-B044, a European Research Council (ERC) Advanced Grant “ELVER” under the European Union’s Horizon 2020 research and innovation programme (grant agreement no. 789108), and additional funding from Google. The opinions, findings, and conclusions or recommendations expressed in this material are those of the authors and do not necessarily reflect the views of the Air Force Research Laboratory (AFRL).

<!-- ====================================================================== -->

{{ todo("
Further topics:

- doubly linked lists
- Trees: - deep copy - sum - maybe the accumulating sum
- cn_function
- pack
- bitwise functions (operators are not present in the logical language)
- 'ownership' in Rust vs. CN
- tips amnd tricks --
  cf. [](https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-verification)
- more data structures to try out
  [](https://www.geeksforgeeks.org/data-structures/#most-popular-data-structures)
- Maybe add some explanation of -- or at least a pointer to --
  Dhruv's Iris-in-C examples:
  pop_queue_lemma_stages.c
  push_queue_induction.c
  pop_queue_unified.c

Further exercises:

- Some exercises that get THEM to write predicates, datatype
  declarations, etc.

Misc things to do:

- replace 0 with NULL in specs

- naming issues - rename == to ptr_eq everywhere in specs - rename list to List in filenames. or go more radical and rename List to cnlist - consider renaming SLList_At to just List (and sllist to just list,
  etc.) everywhere (since we are only dealing with one kind of list
  in the tutorial, the extra pedantry is not getting us much; and
  this simplification would avoid trying to fix conventions that all
  CN code should use everywhere...)

  - related: the name Cons is awkward for several reasons:
    - long / verbose (nothing to do about that, I guess)
    - Seq is capitalized, but it means List
    - most important part is buried in the middle
    - What are the established C conventions here??

- some of the examples use int while the exercises that follow use
  unsigned int. This is a needless source of potential confusion.

- everyplace we do storage allocation, we should really allow the
  malloc call to return NULL if it wants to; the caller should
  explicitly check that it didn't get back NULL. This requires
  defining an 'exit' function with trivial pre- and postconditions
  (true / false).

- In queue.c, when I tried /_@ unfold QueueAux (F.front, F.back,
  B.first); @_/ I was confused by 'the specification function
  `QueueAux' is not declared'. I guess this is, again, the
  distinction between functions and predicates...?

- In debugging the queue example, The fact that some of the
  constraints in the error report are forced while others are random
  values filled in by the SMT solver is pretty problematic...

---

For later:

Alternative formatting tools to consider at some point (not now!):
probably the best fit:
[](https://myst-parser.readthedocs.io/en/latest/)
another very standard one to consider:
alternative: [](https://www.sphinx-doc.org/en/master/index.html)

Misc notes:

- Nb: take V = RW<t>(p) === p |-t-> V
") }}
