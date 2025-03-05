# Block resources

Aside from the `Owned` resources seen so far, CN has another
built-in type of resource called `Block`. Given a C-type `T` and
pointer `p`, `Block<T>(p)` asserts the same ownership as
`Owned<T>(p)` — ownership of a memory cell at `p` the size of type
`T` — but, in contrast to `Owned`, `Block` memory is not assumed
to be initialised.

CN uses this distinction to prevent reads from uninitialised memory:

- A read at C-type `T` and pointer `p` requires a resource
  `Owned<T>(p)`, i.e., ownership of _initialised_ memory at the
  right C-type. The load returns the `Owned` resource unchanged.

- A write at C-type `T` and pointer `p` needs only a
`Block<T>(p)` (so, unlike reads, writes to uninitialised memory
are fine). The write consumes ownership of the `Block` resource
(it destroys it) and returns a new resource `Owned<T>(p)` with the
value written as the output. This means the resource returned from a
write records the fact that this memory cell is now initialised and
can be read from.
<span style="color:red">
BCP: Not sure I understand "returns a new resource `Owned<T>(p)` with the value written as the output" -- perhaps in part because I don't understand what the output of a resource means when the resource is not in the context o a take expression. 
</span>

Since `Owned` carries the same ownership as `Block`, just with the
additional information that the `Owned` memory is initalised, a
resource `Owned<T>(p)` is "at least as good" as `Block<T>(p)` —
an `Owned<T>(p)` resource can be used whenever `Block<T>(p)` is
needed. For instance CN’s type checking of a write to `p` requires a
`Block<T>(p)`, but if an `Owned<T>(p)` resource is what is
available, this can be used just the same. This allows an
already-initialised memory cell to be over-written again.

Unlike `Owned`, whose output is the pointee value, `Block` has no meaningful output.

