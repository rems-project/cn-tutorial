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

