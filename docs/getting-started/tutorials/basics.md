# cn Basics

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
