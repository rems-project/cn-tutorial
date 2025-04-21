# Understanding and controlling test distributions

Automatic test generation is powerful,
but it has its limits,
so it is important to understand how the tests are performing.

We'll explore:

- how to generate coverage reports
- get information about specific test inputs
- adjust the distribution of inputs

## Coverage reports using `lcov`

- `--coverage`
    - `lcov` reports
    - Only line coverage
    - For entire test run

## Analytics with Tyche

- Tyche
    - Per test input information
    - VSCode interface only?

## Tweaking the distributions

- Using `assert` to skew distributions
  {{ todo("Ideally, should support multiple specs, with some for testing only") }}
    - Comparison to partition testing
- `--max-array-length`?
