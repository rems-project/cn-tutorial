# What is CN?

CN enables you to write special comments in your code – called specifications –
that describe what you expect it to do, any assumptions it makes about input,
and any assurances it makes  about output.

The CN tools work together to ensure that your code matches its specification.

!!! info inline end "Not yet implemented"
    `cn test` is not yet available.

* Runtime testing – `cn test`.  CN produces an instrumented debug build of your
  code that translates your specifications to runtime assertions that test if the
  specs hold for that specific execution.  This works with existing unit and
  integration tests and is the easiest way to get started.

* Property-based testing – `cn generate-tests` .  Runtime testing is limited to
  the test input you've created in your test suite.  CN property-based testing
  tool automatically generates new input for unit tests.  It works with CN's
  runtime testing to increase the chances that your tests find bugs.

* Verification – `cn verify` .  In many cases, CN can automatically verify that
  your specifications hold for all possible inputs without ever running the code.
  CN uses an SMT solver to prove that your specs hold – when it works, it
  provides a very high degree of assurance.  But not all specs can be proved
  automatically.  CN provides a debugger for investigating when automated
  verification fails and how to fix it.

Next, you'll learn how to install CN's runtime testing, property-based testing,
and verification tools, along with a VSCode plugin for writing CN
specifications.
