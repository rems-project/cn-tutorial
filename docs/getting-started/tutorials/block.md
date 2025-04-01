# W resources

Aside from the `RW` resources seen so far, CN has another
built-in type of resource called `W`. Given a C-type `T` and
pointer `p`, `W<T>(p)` asserts the same ownership as
`RW<T>(p)` — ownership of a memory cell at `p` the size of type
`T` — but, in contrast to `RW`, `W` memory is not assumed
to be initialised.

CN uses this distinction to prevent reads from uninitialised memory:

- A read at C-type `T` and pointer `p` requires a resource
  `RW<T>(p)`, i.e., ownership of _initialised_ memory at the
  right C-type. The load returns the `RW` resource unchanged.

- A write at C-type `T` and pointer `p` needs only a
`W<T>(p)` (so, unlike reads, writes to uninitialised memory
are fine). The write consumes ownership of the `W` resource
(it destroys it) and returns a new resource `RW<T>(p)` with the
value written as the output. This means the resource returned from a
write records the fact that this memory cell is now initialised and
can be read from.
{{ todo("BCP: Not sure I understand 'returns a new resource `RW<T>(p)` with the value written as the output' -- perhaps in part because I don't understand what the output of a resource means when the resource is not in the context o a take expression. ") }}

Since `RW` carries the same ownership as `W`, just with the
additional information that the `RW` memory is initalised, a
resource `RW<T>(p)` is "at least as good" as `W<T>(p)` —
an `RW<T>(p)` resource can be used whenever `W<T>(p)` is
needed. For instance CN’s type checking of a write to `p` requires a
`W<T>(p)`, but if an `RW<T>(p)` resource is what is
available, this can be used just the same. This allows an
already-initialised memory cell to be over-written again.

Unlike `RW`, whose output is the pointee value, `W` has no meaningful output.

